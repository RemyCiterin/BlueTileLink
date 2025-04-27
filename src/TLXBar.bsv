import TLTypes :: *;
import Vector :: *;
import Utils :: *;
import Fifo :: *;
import Ehr :: *;

`include "TL.defines"


// This package defines N*M cross bar interconnects, to root the TileLink packets, it use
// - The address in channels A and C
// - The source in channels B and D
// - The sink in channel E
typedef struct {
  // If true, enable channels B,C and E (coherency), otherwise, keep those
  // channels empty
  Bool bce;

  function Token#(m) fn(Bit#(sourceW) source) rootSource;
  function Token#(n) fn(Bit#(sinkW) sink) rootSink;
  function Token#(n) fn(Bit#(addrW) addr) rootAddr;
} XBarConf#(numeric type n, numeric type m, `TL_ARGS_DECL);

interface XBar#(numeric type n, numeric type m, `TL_ARGS_DECL);
  interface Vector#(n, TLMaster#(`TL_ARGS)) masters;
  interface Vector#(m, TLSlave#(`TL_ARGS)) slaves;
endinterface

module mkXBar#(XBarConf#(n,m,`TL_ARGS) conf) (XBar#(n,m,`TL_ARGS));
  Fifo#(2, ChannelA#(`TL_ARGS)) fifoA <- mkFifo;
  Fifo#(2, ChannelB#(`TL_ARGS)) fifoB <- mkFifo;
  Fifo#(2, ChannelC#(`TL_ARGS)) fifoC <- mkFifo;
  Fifo#(2, ChannelD#(`TL_ARGS)) fifoD <- mkFifo;
  Fifo#(2, ChannelE#(`TL_ARGS)) fifoE <- mkFifo;

  TLSize dataSize = fromInteger(valueOf(dataW));

  Reg#(Token#(m)) tokenA <- mkReg(?);
  Reg#(Token#(m)) tokenC <- mkReg(?);
  Reg#(Token#(n)) tokenD <- mkReg(?);
  Reg#(TLSize) sizeA <- mkReg(0);
  Reg#(TLSize) sizeC <- mkReg(0);
  Reg#(TLSize) sizeD <- mkReg(0);

  if (!conf.bce) begin
    fifoB = nullFifo;
    fifoC = nullFifo;
    fifoE = nullFifo;
  end

  Vector#(n, TLMaster#(`TL_ARGS)) inputs = newVector;
  Vector#(m, TLSlave#(`TL_ARGS)) outputs = newVector;

  for (Integer i=0; i < valueOf(n); i = i + 1) begin
    Bool canDeqA =
      fifoA.canDeq && fromInteger(i) == conf.rootAddr(fifoA.first.address);

    Bool canDeqC =
      fifoC.canDeq && fromInteger(i) == conf.rootAddr(fifoC.first.address);

    Bool canEnqD =
      fifoD.canEnq && (sizeD == 0 || fromInteger(i) == tokenD);

    Bool canDeqE =
      fifoE.canDeq && fromInteger(i) == conf.rootSink(fifoE.first.sink);

    inputs[i] = interface TLMaster;
      interface FifoO channelA;
        method canDeq = canDeqA;
        method deq = when(canDeqA, fifoA.deq);
        method first = when(canDeqA, fifoA.first);
      endinterface

      interface channelB = toFifoI(fifoB);

      interface FifoO channelC;
        method canDeq = canDeqC;
        method deq = when(canDeqC, fifoC.deq);
        method first = when(canDeqC, fifoC.first);
      endinterface

      interface FifoI channelD;
        method canEnq = canEnqD;
        method Action enq(ChannelD#(`TL_ARGS) msg) if (canEnqD);
          action
            let size = sizeD == 0 ? 1 << msg.size : sizeD;
            sizeD <= size < dataSize || !hasDataD(msg.opcode) ? 0 : size - dataSize;
            tokenD <= fromInteger(i);
            fifoD.enq(msg);
          endaction
        endmethod
      endinterface

      interface FifoO channelE;
        method canDeq = canDeqE;
        method deq = when(canDeqE, fifoE.deq);
        method first = when(canDeqE, fifoE.first);
      endinterface
    endinterface;
  end

  for (Integer i=0; i < valueOf(m); i = i + 1) begin
    Bool canEnqA =
      fifoA.canEnq && (sizeA == 0 || fromInteger(i) == tokenA);

    Bool canDeqB =
      fifoB.canDeq && fromInteger(i) == conf.rootSource(fifoB.first.source);

    Bool canEnqC =
      fifoC.canEnq && (sizeC == 0 || fromInteger(i) == tokenC);

    Bool canDeqD =
      fifoD.canDeq && fromInteger(i) == conf.rootSource(fifoD.first.source);

    outputs[i] = interface TLSlave;
      interface FifoI channelA;
        method canEnq = canEnqA;
        method Action enq(ChannelA#(`TL_ARGS) msg) if (canEnqA);
          action
            let size = sizeA == 0 ? 1 << msg.size : sizeA;
            sizeA <= size < dataSize || !hasDataA(msg.opcode) ? 0 : size - dataSize;
            tokenA <= fromInteger(i);
            fifoA.enq(msg);
          endaction
        endmethod
      endinterface

      interface FifoO channelB;
        method canDeq = canDeqB;
        method deq = when(canDeqB, fifoB.deq);
        method first = when(canDeqB, fifoB.first);
      endinterface

      interface FifoI channelC;
        method canEnq = canEnqC;
        method Action enq(ChannelC#(`TL_ARGS) msg) if (canEnqC);
          action
            let size = sizeC == 0 ? 1 << msg.size : sizeC;
            sizeC <= size < dataSize || !hasDataC(msg.opcode) ? 0 : size - dataSize;
            tokenC <= fromInteger(i);
            fifoC.enq(msg);
          endaction
        endmethod
      endinterface

      interface FifoO channelD;
        method canDeq = canDeqD;
        method deq = when(canDeqD, fifoD.deq);
        method first = when(canDeqD, fifoD.first);
      endinterface

      interface channelE = toFifoI(fifoE);
    endinterface;
  end

  interface masters = inputs;
  interface slaves = outputs;
endmodule
