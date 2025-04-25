import Ehr :: *;
import Fifo :: *;
import BlockRam :: *;
import StmtFSM :: *;
import Vector :: *;
import BuildVector :: *;
import BCache :: *;
import Utils :: *;

import TLServer :: *;
import TLClient :: *;
import TLBram :: *;

import TLTypes :: *;

module mkCPU(Empty);
endmodule

typedef 32 AddrW;
typedef 4 DataW;
typedef 4 SinkW;
typedef 8 SourceW;
typedef 8 SizeW;

typedef 2 NCache;

module mkCPU_SIM(Empty);
  Reg#(Bit#(32)) cycle <- mkReg(0);

  rule count_cycle;
    cycle <= cycle + 1;
    if (cycle == 4096 + 200000) begin
      $display("timeout!");
      $finish;
    end
  endrule

  Fifo#(TAdd#(2, NCache), ChannelA#(AddrW, DataW, SizeW, SourceW, SinkW)) channelA <- mkFifo;
  Fifo#(TAdd#(2, NCache), ChannelB#(AddrW, DataW, SizeW, SourceW, SinkW)) channelB <- mkFifo;
  Fifo#(TAdd#(2, NCache), ChannelC#(AddrW, DataW, SizeW, SourceW, SinkW)) channelC <- mkFifo;
  Fifo#(TAdd#(2, NCache), ChannelD#(AddrW, DataW, SizeW, SourceW, SinkW)) channelD <- mkFifo;
  Fifo#(TAdd#(2, NCache), ChannelE#(AddrW, DataW, SizeW, SourceW, SinkW)) channelE <- mkFifo;

  let slave = interface TLSlave;
    interface channelA = toFifoI(channelA);
    interface channelB = toFifoO(channelB);
    interface channelC = toFifoI(channelC);
    interface channelD = toFifoO(channelD);
    interface channelE = toFifoI(channelE);
  endinterface;

  let master = interface TLMaster;
    interface channelA = toFifoO(channelA);
    interface channelB = toFifoI(channelB);
    interface channelC = toFifoO(channelC);
    interface channelD = toFifoI(channelD);
    interface channelE = toFifoO(channelE);
  endinterface;

  BramBE#(Bit#(32), 4) rom <- mkSizedBramInitBE(4096, 0);

  Bit#(sizeW) logSize = 6;

  Vector#(NCache, TLSlave#(AddrW, DataW, SizeW, SourceW, SinkW)) slaves <-
    mkVectorTLSlave(slave);

  function Bit#(32) encode(Bit#(20) tag, Bit#(6) index, Bit#(4) offset) =
    {tag, index, offset, 0};

  function Tuple3#(Bit#(20),Bit#(6),Bit#(4)) decode(Bit#(32) addr) =
    tuple3(addr[31:12], addr[11:6], addr[5:2]);

  Integer nCache = valueOf(NCache);
  Vector#(NCache, BCacheCore#(Bit#(1), Bit#(20), Bit#(6), Bit#(4), AddrW, DataW, SizeW, SourceW, SinkW))
    caches <- mapM(mkBCacheCore(BCacheConf{encode: encode, decode: decode}), slaves);

  Vector#(NCache, Bit#(SourceW)) sources = Vector::genWith(fromInteger);

  let rom_controller <- mkTLBram(rom);
  mkTileLinkClientFSM(0, logSize, master, rom_controller, sources);

  Vector#(NCache, Reg#(Bit#(32))) response <- replicateM(mkReg(0));

  Vector#(NCache, Stmt) lock = ?;
  Vector#(NCache, Action) read = ?;
  Vector#(NCache, Stmt) unlock = ?;
  Vector#(NCache, Stmt) increment = ?;
  for (Integer i=0; i < nCache; i = i + 1) begin
    read[i] = action
      let x <- caches[i].response;
      response[i] <= x;
    endaction;

    lock[i] = seq
      response[i] <= 0;

      while (response[i] == 0) seq
        caches[i].start(0,0);
        caches[i].matching(0, LoadReserve);
        read[i];
        $display(cycle, " try %d is %s", i, response[i] == 0 ? "success" : "fail");
        if (response[i] == 0) seq
          caches[i].start(0,0);
          caches[i].matching(0,tagged StoreConditional {mask: 1, data: 1});
          action
            let x <- caches[i].success;
            $display(cycle, " success: %b", x);
            response[i] <= x ? 1 : 0;
          endaction
        endseq else
          response[i] <= 0;
      endseq
    endseq;

    unlock[i] = seq
      caches[i].start(0,0);
      caches[i].matching(0, tagged Store {data: 0, mask: 1});
    endseq;

    increment[i] = seq
      caches[i].start(2,0);
      caches[i].matching(1, Load);
      read[i];

      caches[i].start(1,0);
      caches[i].matching(0, Load);
      read[i];
      $display(cycle, " counter %d: %d at %d", i, response[i], cycle);
      caches[i].start(1,0);
      caches[i].matching(0, tagged Store {data: response[i]+1, mask: 15});
    endseq;
  end

  Stmt initCaches = seq noAction; endseq;
  for (Integer i=0; i < nCache; i = i + 1) begin
    initCaches = seq
      caches[i].setSource(fromInteger(i));
      initCaches;
    endseq;
  end

  Reg#(Bit#(32)) counter <- mkReg(0);

  Stmt main = seq noAction; endseq;
  for (Integer i=0; i < nCache; i = i + 1) begin
    main = seq
      par
        main;
        seq
          while (True) seq
            lock[i];
            increment[i];
            doAssert(counter == response[i], "ERROR!");
            counter <= counter + 1;
            unlock[i];
            //delay(100);
          endseq
        endseq
      endpar
    endseq;
  end

  Stmt stmt = seq
    initCaches;
    main;
    $finish;
  endseq;

  mkAutoFSM(stmt);
endmodule
