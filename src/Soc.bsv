import Ehr :: *;
import Fifo :: *;
import BlockRam :: *;
import StmtFSM :: *;

import Server :: *;

import TLTypes :: *;

`include "CC.defines"

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

  Fifo#(1, ChannelA#(AddrW, DataW, SizeW, SourceW, SinkW)) channelA <- mkPipelineFifo;
  Fifo#(1, ChannelB#(AddrW, DataW, SizeW, SourceW, SinkW)) channelB <- mkPipelineFifo;
  Fifo#(1, ChannelC#(AddrW, DataW, SizeW, SourceW, SinkW)) channelC <- mkPipelineFifo;
  Fifo#(1, ChannelD#(AddrW, DataW, SizeW, SourceW, SinkW)) channelD <- mkPipelineFifo;
  Fifo#(1, ChannelE#(AddrW, DataW, SizeW, SourceW, SinkW)) channelE <- mkPipelineFifo;

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

  Bram#(Bit#(32), Bit#(32)) bramCore <- mkSizedBramInit(4096, 0);
  Bram#(Bit#(32), Bit#(32)) bram = interface Bram;
    method Action write(Bit#(32) index, Bit#(32) data);
      $display("BRAM at %d: write addr: %h data: %h", cycle, index, data);
      bramCore.write(index, data);
    endmethod

    method Action read(Bit#(32) index);
      $display("BRAM at %d: read request addr: %h", cycle, index);
      bramCore.read(index);
    endmethod

    method response = bramCore.response;
    method canDeq = bramCore.canDeq;

    method Action deq;
      action
        $display("BRAM at %d: read response data: %h", cycle, bramCore.response);
        bramCore.deq;
      endaction
    endmethod
  endinterface;

  AcquireFSM#(Bit#(32), AddrW, DataW, SizeW, SourceW, SinkW) acquireM <-
    mkAcquireFSM(4, bram, slave);

  ReleaseFSM#(Bit#(32), AddrW, DataW, SizeW, SourceW, SinkW) releaseM <-
    mkReleaseFSM(4, bram, slave);

  ProbeFSM#(Bit#(32), AddrW, DataW, SizeW, SourceW, SinkW) probeM <-
    mkProbeFSM(4, bram, slave);

  Reg#(PermTL) probePerm <- mkReg(?);
  Reg#(Bit#(AddrW)) probeAddr <- mkReg(?);

  Stmt stmt = seq
    $display("Start BlueCoherent TestBench!");
    acquireM.setSource(9);
    releaseM.setSource(12);
    probeM.setSource(12);

    par
      seq
        par
          seq
            acquireM.acquireBlock(NtoT, 0, 0);
            action
              let perms <- acquireM.acquireAck();
              $display("CACHE at %d: perms: ", cycle, fshow(perms));
            endaction

            releaseM.releaseBlock(TtoN, 0, 0);
            releaseM.releaseAck();
          endseq

          seq
            while (True) par
              action
                match {.addr, .perm} <- probeM.probeBlock();
                $display("PROBE at %d: probe at address %h", cycle, addr);
                probeAddr <= addr;
                probePerm <= perm;
              endaction

              probeM.probeAck(probePerm == N ? TtoN : TtoB, 0);
              probeM.probeFinish;
            endpar
          endseq
        endpar
      endseq

      seq
        $display("channelA: ", fshow(channelA.first));
        repeat(4) channelD.enq(ChannelD{
          opcode: GrantData(T),
          size: channelA.first.size,
          source: channelA.first.source,
          sink: 0,
          data: 42
        });
        channelA.deq;

        repeat(4) channelC.deq;
        channelD.enq(ChannelD{
          opcode: ReleaseAck,
          size: 4,
          source: 12,
          sink: 0,
          data: ?
        });

        par
          channelB.enq(ChannelB{
            opcode: ProbeBlock(N),
            address: 0,
            size: 4,
            source: 12
          });
          repeat(4) channelC.deq;

          channelB.enq(ChannelB{
            opcode: ProbeBlock(N),
            address: 0,
            size: 4,
            source: 12
          });
          repeat(4) channelC.deq;
        endpar
      endseq
    endpar

    $finish;
  endseq;

  mkAutoFSM(stmt);
endmodule


