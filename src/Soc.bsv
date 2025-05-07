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
import MSHR :: *;
import NBCache :: *;
import TLXBar :: *;

import Connectable :: *;
import PLRU :: *;

module mkCPU(Empty);
endmodule

typedef 32 AddrW;
typedef 4 DataW;
typedef 8 SizeW;
typedef 8 SourceW;
typedef 4 SinkW;

typedef 2 NCache;

typedef 2 MSHR;

(* synthesize *)
module mkTestNBCache#(Vector#(TAdd#(MSHR,1), Bit#(SourceW)) sources)
  (TLMaster#(AddrW, DataW, SizeW, SourceW, SinkW));

  function Bit#(32) encode(Bit#(20) tag, Bit#(6) index, Bit#(4) offset) =
    {tag, index, offset, 0};

  function Tuple3#(Bit#(20),Bit#(6),Bit#(4)) decode(Bit#(32) addr) =
    tuple3(addr[31:12], addr[11:6], addr[5:2]);

  NBCacheCore#(MSHR, 4, Bit#(20), Bit#(6), Bit#(4), AddrW, DataW, SizeW, SourceW, SinkW)
    cache <- mkNBCacheCore(NBCacheConf{encode: encode, decode: decode});

  rule init;
    $display(fshow(sources));
    cache.setSources(sources);
  endrule

  rule free;
    let m <- cache.free;
    $display("free %d", m);
  endrule

  // We use more addresses than the number of MSHR for this test
  Vector#(32, Reg#(NBCacheAck#(MSHR))) mshr <- replicateM(mkReg(?));
  Vector#(32, Reg#(Bit#(32))) response <- replicateM(mkReg(?));

  function Stmt read(Token#(32) id, Bit#(20) tag, Bit#(6) index, Bit#(4) offset) = seq
    mshr[id] <= Blocked;

    while (mshr[id] != Success) seq
      cache.lookup(index,offset,True,?,?);
      action
        let m <- cache.matching(tag);
        mshr[id] <= m;
      endaction
    endseq

    action
      let r <- cache.response;
      response[id] <= r;
      $display("%h == mem[%h]", r, {tag,index,offset,2'b0});
    endaction
  endseq;

  function Stmt
    write(Token#(32) id, Bit#(20) tag, Bit#(6) index, Bit#(4) offset, Bit#(32) data) = seq
    mshr[id] <= Blocked;

    while (mshr[id] != Success) seq
      cache.lookup(index, offset, False, data, -1);
      $display("lookup %h", {tag,index,offset,2'b0});
      action
        let m <- cache.matching(tag);
        $display("status: ", fshow(m));
        mshr[id] <= m;

        if (m == Success) $display("mem[%h] <= %h", {tag,index,offset,2'b0}, data);
      endaction
    endseq
  endseq;

  Stmt main = seq
    par
      write(0,0,0,0,42);
      write(1,1,0,0,41);
      write(2,2,0,0,43);
    endpar

    par
      read(0,0,0,0);
      read(1,1,0,0);
      read(2,2,0,0);
    endpar

    while (True) noAction;
  endseq;

  mkAutoFSM(main);

  Fifo#(2, ChannelA#(32,2,8,8,4)) fifoA <- mkFifo;
  Fifo#(2, ChannelB#(32,2,8,8,4)) fifoB <- mkFifo;
  Fifo#(2, ChannelC#(32,2,8,8,4)) fifoC <- mkFifo;
  Fifo#(2, ChannelD#(32,2,8,8,4)) fifoD <- mkFifo;
  Fifo#(2, ChannelE#(32,2,8,8,4)) fifoE <- mkFifo;

  mkDecreaseWidth(True, cache.master, interface TLSlave;
    interface channelA = toFifoI(fifoA);
    interface channelB = toFifoO(fifoB);
    interface channelC = toFifoI(fifoC);
    interface channelD = toFifoO(fifoD);
    interface channelE = toFifoI(fifoE);
  endinterface);

  Fifo#(2, ChannelA#(32,4,8,8,4)) outA <- mkFifo;
  Fifo#(2, ChannelB#(32,4,8,8,4)) outB <- mkFifo;
  Fifo#(2, ChannelC#(32,4,8,8,4)) outC <- mkFifo;
  Fifo#(2, ChannelD#(32,4,8,8,4)) outD <- mkFifo;
  Fifo#(2, ChannelE#(32,4,8,8,4)) outE <- mkFifo;

  mkIncreaseWidth(True, interface TLMaster;
    interface channelA = toFifoO(fifoA);
    interface channelB = toFifoI(fifoB);
    interface channelC = toFifoO(fifoC);
    interface channelD = toFifoI(fifoD);
    interface channelE = toFifoO(fifoE);
  endinterface, interface TLSlave;
    interface channelA = toFifoI(outA);
    interface channelB = toFifoO(outB);
    interface channelC = toFifoI(outC);
    interface channelD = toFifoO(outD);
    interface channelE = toFifoI(outE);
  endinterface);

  interface channelA = toFifoO(outA);
  interface channelB = toFifoI(outB);
  interface channelC = toFifoO(outC);
  interface channelD = toFifoI(outD);
  interface channelE = toFifoO(outE);
endmodule

interface TestBCache;
  interface TLMaster#(AddrW, DataW, SizeW, SourceW, SinkW) master;
  method Action incr;

  method Action readCounter(Bit#(32) count);
endinterface

(* synthesize *)
module mkTestBCache#(Bit#(SourceW) source) (TestBCache);
  // Ensure that we always have enough ressources for the next cache miss
  Fifo#(MSHR, ChannelA#(AddrW, DataW, SizeW, SourceW, SinkW)) fifoA <- mkFifo;
  Fifo#(2, ChannelB#(AddrW, DataW, SizeW, SourceW, SinkW)) fifoB <- mkFifo;
  Fifo#(2, ChannelC#(AddrW, DataW, SizeW, SourceW, SinkW)) fifoC <- mkFifo;
  Fifo#(2, ChannelD#(AddrW, DataW, SizeW, SourceW, SinkW)) fifoD <- mkFifo;
  Fifo#(2, ChannelE#(AddrW, DataW, SizeW, SourceW, SinkW)) fifoE <- mkFifo;

  let slave = interface TLSlave;
    interface channelA = toFifoI(fifoA);
    interface channelB = toFifoO(fifoB);
    interface channelC = toFifoI(fifoC);
    interface channelD = toFifoO(fifoD);
    interface channelE = toFifoI(fifoE);
  endinterface;

  function Bit#(32) encode(Bit#(20) tag, Bit#(6) index, Bit#(4) offset) =
    {tag, index, offset, 0};

  function Tuple3#(Bit#(20),Bit#(6),Bit#(4)) decode(Bit#(32) addr) =
    tuple3(addr[31:12], addr[11:6], addr[5:2]);

  Integer nCache = valueOf(NCache);
  BCacheCore#(2, Bit#(20), Bit#(6), Bit#(4), AddrW, DataW, SizeW, SourceW, SinkW)
    cache <- mkBCacheCore(BCacheConf{encode: encode, decode: decode},slave);

  rule setSource;
    cache.setSource(source);
  endrule

  Wire#(Bit#(32)) counter <- mkBypassWire;

  Reg#(Bit#(32)) cycle <- mkReg(0);
  rule incrCycle;
    cycle <= cycle + 1;
  endrule

  Reg#(Bit#(32)) response <- mkReg(?);

  Action read = action
    let x <- cache.response;
    response <= x;
  endaction;

  Stmt lock = seq
    response <= 0;

    while (response == 0) seq
      cache.lookup(0,0);
      cache.matching(0, LoadReserve);
      read;
      $display(cycle, " try %d is %s", source, response == 0 ? "success" : "fail");
      if (response == 0) seq
        cache.lookup(0,0);
        cache.matching(0,tagged StoreConditional {mask: 1, data: 1});
        action
          let x <- cache.success;
          $display(cycle, " success: %b", x);
          response <= x ? 1 : 0;
        endaction
      endseq else
        response <= 0;
    endseq
  endseq;

  Stmt unlock = seq
    cache.lookup(0,0);
    cache.matching(0, tagged Store {data: 0, mask: 1});
  endseq;

  Stmt increment = seq
    cache.lookup(2,0);
    cache.matching(1, Load);
    read;

    cache.lookup(1,0);
    cache.matching(0, Load);
    read;
    $display(cycle, " counter %d: %d at %d", source, response, cycle);
    cache.lookup(1,0);
    cache.matching(0, tagged Store {data: response+1, mask: 15});
  endseq;

  Fifo#(2, void) incrQ <- mkFifo;

  Stmt main = seq
    while (True) seq
      lock;
      increment;
      doAssert(counter == response, "ERROR!");
      incrQ.enq(?);
      while (incrQ.canDeq) noAction;
      unlock;
      //delay(100);
    endseq
  endseq;

  mkAutoFSM(main);

  method incr = incrQ.deq;

  method readCounter = counter._write;

  interface TLMaster master;
    interface channelA = toFifoO(fifoA);
    interface channelB = toFifoI(fifoB);
    interface channelC = toFifoO(fifoC);
    interface channelD = toFifoI(fifoD);
    interface channelE = toFifoO(fifoE);
  endinterface
endmodule

(* synthesize *)
module mkCPU_SIM(Empty);
  Reg#(Bit#(32)) cycle <- mkReg(0);

  rule count_cycle;
    cycle <= cycle + 1;
    if (cycle == 4096 + 200000) begin
      $display("timeout!");
      $finish;
    end
  endrule

  Fifo#(2, ChannelA#(AddrW, DataW, SizeW, SourceW, SinkW)) channelA <- mkFifo;
  Fifo#(2, ChannelB#(AddrW, DataW, SizeW, SourceW, SinkW)) channelB <- mkFifo;
  Fifo#(2, ChannelC#(AddrW, DataW, SizeW, SourceW, SinkW)) channelC <- mkFifo;
  Fifo#(2, ChannelD#(AddrW, DataW, SizeW, SourceW, SinkW)) channelD <- mkFifo;
  Fifo#(2, ChannelE#(AddrW, DataW, SizeW, SourceW, SinkW)) channelE <- mkFifo;

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

  Integer nCache = valueOf(NCache);

  Reg#(Bit#(32)) counter <- mkReg(0);

  Vector#(NCache, Bit#(SourceW)) bsources = Vector::genWith(fromInteger);
  Vector#(NCache, TestBCache) caches <- mapM(mkTestBCache, bsources);

  Vector#(MSHR, Bit#(SourceW)) nbsources = Vector::genWith(fromInteger);
  nbsources = Vector::map(add(fromInteger(nCache)), nbsources);
  let nbcache <- mkTestNBCache(append(take(nbsources),nbsources));

  function Bit#(0) rootSink(Bit#(SinkW) sink) = 0;
  function Bit#(0) rootAddr(Bit#(AddrW) addr) = 0;
  function Bit#(TLog#(TAdd#(NCache,MSHR))) rootSource(Bit#(SourceW) source) =
    truncate(min(fromInteger(nCache),source));

  let conf = XBarConf{
    bce: True,
    rootSink: rootSink,
    rootSource: rootSource,
    rootAddr: rootAddr
  };

  XBar#(1, TAdd#(NCache,MSHR), AddrW, DataW, SizeW, SourceW, SinkW) xbar <- mkXBar(conf);

  mkConnection(xbar.slaves[nCache], nbcache);
  mkConnection(xbar.masters[0], slave);
  for (Integer i=0; i < nCache; i = i + 1) begin
    mkConnection(xbar.slaves[i], caches[i].master);

    rule incr;
      caches[i].incr;
      counter <= counter + 1;
    endrule

    rule readCounter;
      caches[i].readCounter(counter);
    endrule
  end

  function Bit#(SourceW) repr(Bit#(SourceW) source);
    return source >= fromInteger(nCache) ? fromInteger(nCache) : source;
  endfunction

  let rom_controller <- mkTLBram(rom);
  mkTileLinkClientFSM(
    0,
    logSize,
    master,
    rom_controller,
    repr,
    append(vec(fromInteger(nCache)),bsources)
  );
endmodule
