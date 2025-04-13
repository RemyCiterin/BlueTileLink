import Ehr :: *;
import Fifo :: *;
import BlockRam :: *;
import StmtFSM :: *;
import Vector :: *;
import BuildVector :: *;

import Server :: *;
import Client :: *;

import TLTypes :: *;

module mkCPU(Empty);
endmodule

typedef 32 AddrW;
typedef 4 DataW;
typedef 4 SinkW;
typedef 4 SourceW;
typedef 8 SizeW;

module mkCPU_SIM(Empty);
  Reg#(Bit#(32)) cycle <- mkReg(0);

  rule count_cycle;
    cycle <= cycle + 1;
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

  Bram#(Bit#(32), Bit#(32)) cacheCore <- mkSizedBramInit(4096, 0);
  Bram#(Bit#(32), Bit#(32)) bram = interface Bram;
    method Action write(Bit#(32) index, Bit#(32) data);
      $display("CACHE at %d: write addr: %h data: %h", cycle, index, data);
      cacheCore.write(index, data);
    endmethod

    method Action read(Bit#(32) index);
      $display("CACHE at %d: read request addr: %h", cycle, index);
      cacheCore.read(index);
    endmethod

    method response = cacheCore.response;
    method canDeq = cacheCore.canDeq;

    method Action deq;
      action
        $display("CACHE at %d: read response data: %h", cycle, cacheCore.response);
        cacheCore.deq;
      endaction
    endmethod
  endinterface;

  Bram#(Bit#(32), Bit#(32)) romCore <- mkSizedBramInit(4096, 0);
  Bram#(Bit#(32), Bit#(32)) rom = interface Bram;
    method Action write(Bit#(32) index, Bit#(32) data);
      $display("ROM at %d: write addr: %h data: %h", cycle, index, data);
      romCore.write(index, data);
    endmethod

    method Action read(Bit#(32) index);
      $display("ROM at %d: read request addr: %h", cycle, index);
      romCore.read(index);
    endmethod

    method response = romCore.response;
    method canDeq = romCore.canDeq;

    method Action deq;
      action
        $display("ROM at %d: read response data: %h", cycle, romCore.response);
        romCore.deq;
      endaction
    endmethod
  endinterface;

  Vector#(2, TLSlave#(AddrW, DataW, SizeW, SourceW, SinkW)) slaves <-
    mkVectorTLSlave(slave);

  AcquireFSM#(Bit#(32), AddrW, DataW, SizeW, SourceW, SinkW) acquireM1 <-
    mkAcquireFSM(4, bram, slaves[0]);

  ReleaseFSM#(Bit#(32), AddrW, DataW, SizeW, SourceW, SinkW) releaseM1 <-
    mkReleaseFSM(4, bram, slaves[0]);

  AcquireFSM#(Bit#(32), AddrW, DataW, SizeW, SourceW, SinkW) acquireM2 <-
    mkAcquireFSM(4, bram, slaves[0]);

  ReleaseFSM#(Bit#(32), AddrW, DataW, SizeW, SourceW, SinkW) releaseM2 <-
    mkReleaseFSM(4, bram, slaves[0]);

  mkTileLinkClientFSM(0, 4, master, rom, vec(12, 4));

  Reg#(PermTL) probePerm1 <- mkReg(?);
  Reg#(Bit#(AddrW)) probeAddr1 <- mkReg(?);
  Reg#(PermTL) probePerm2 <- mkReg(?);
  Reg#(Bit#(AddrW)) probeAddr2 <- mkReg(?);

  Stmt stmt = seq
    $display("Start BlueCoherent TestBench!");
    acquireM1.setSource(9);
    releaseM1.setSource(12);

    acquireM2.setSource(5);
    releaseM2.setSource(4);

    par
      seq
        acquireM1.acquireBlock(NtoT, 0, 0);
        action
          let perms <- acquireM1.acquireAck();
          $display("CACHE 0 at %d: perms: ", cycle, fshow(perms));
        endaction

        releaseM1.releaseBlock(TtoN, 0, 0);
        releaseM1.releaseAck();
      endseq

      seq
        acquireM2.acquireBlock(NtoT, 0, 0);
        action
          let perms <- acquireM2.acquireAck();
          $display("CACHE 1 at %d: perms: ", cycle, fshow(perms));
        endaction

        releaseM2.releaseBlock(TtoN, 0, 0);
        releaseM2.releaseAck();
      endseq


      seq
        while (True) par
          action
            match {.addr, .perm} <- releaseM2.probeBlock();
            $display("PROBE at %d: probe at address %h", cycle, addr);
            probeAddr2 <= addr;
            probePerm2 <= perm;
          endaction

          releaseM2.probeAck(probePerm2 == N ? TtoN : TtoB, probeAddr2);
          releaseM2.probeFinish;
        endpar
      endseq


      seq
        while (True) par
          action
            match {.addr, .perm} <- releaseM1.probeBlock();
            $display("PROBE at %d: probe at address %h", cycle, addr);
            probeAddr1 <= addr;
            probePerm1 <= perm;
          endaction

          releaseM1.probeAck(probePerm1 == N ? TtoN : TtoB, probeAddr1);
          releaseM1.probeFinish;
        endpar
      endseq


    endpar
  endseq;

  mkAutoFSM(stmt);
endmodule


