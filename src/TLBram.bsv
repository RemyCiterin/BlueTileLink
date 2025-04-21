// Drive a BRAM module using TileLink Get and Put requests

import TLTypes :: *;
import BlockRam :: *;
import Fifo :: *;
import Ehr :: *;

export mkTLBram;

`include "TL.defines"

typedef enum {
  Idle, Read, Write
} TLBramState deriving(Bits, FShow, Eq);

module mkTLBram#(Bit#(sinkW) sink, BramBE#(Bit#(addrW), dataW) bram) (TLSlave#(`TL_ARGS));
  Bit#(sizeW) logDataW = fromInteger(valueOf(TLog#(dataW)));
  Bit#(addrW) beatLen = fromInteger(valueOf(dataW));

  Fifo#(2, ChannelA#(`TL_ARGS)) fifoA <- mkFifo;
  Fifo#(2, ChannelD#(`TL_ARGS)) fifoD <- mkFifo;
  let message = fifoA.first;

  Ehr#(2, Bit#(addrW)) sizeReg <- mkEhr(?);
  Ehr#(2, Bit#(addrW)) addrReg <- mkEhr(?);

  Ehr#(2, TLBramState) state <- mkEhr(Idle);

  rule receivePutData
    if (message.opcode == PutData);

    Bool first = sizeReg[0] == 0;
    Bit#(addrW) size = first ? (1 << message.size) : sizeReg[0];
    Bit#(addrW) addr = first ? message.address : addrReg[0];

    bram.write(addr >> logDataW, message.data, message.mask);

    fifoA.deq;
    state[0] <= message.last ? Idle : Write;
    sizeReg[0] <= message.last ? 0 : size - beatLen;
    addrReg[0] <= addr + beatLen;

    if (message.last) begin
      fifoD.enq(ChannelD{
        source: message.source,
        size: message.size,
        opcode: AccessAck,
        last: True,
        sink: sink,
        data: ?
      });
    end
  endrule

  rule readBram
    if (state[1] == Read);
    bram.read(addrReg[1] >> logDataW);
  endrule

  rule startGetFull if (message.opcode == GetFull && state[0] == Idle);
    state[0] <= Read;
  endrule

  rule bramResponse if (state[0] == Read);
    Bool first = sizeReg[0] == 0;
    Bit#(addrW) size = first ? (1 << message.size) : sizeReg[0];
    Bit#(addrW) addr = first ? message.address : addrReg[0];
    Bool last = beatLen >= size;

    fifoD.enq(ChannelD{
      source: message.source,
      opcode: AccessAckData,
      data: bram.response,
      size: message.size,
      last: last,
      sink: sink
    });

    bram.deq;
    if (last) fifoA.deq;

    state[0] <= last ? Idle : Read;
    sizeReg[0] <= last ? 0 : size - beatLen;
    addrReg[0] <= addr + beatLen;
  endrule

  interface channelA = toFifoI(fifoA);
  interface channelB = nullFifoO;
  interface channelC = nullFifoI;
  interface channelD = toFifoO(fifoD);
  interface channelE = nullFifoI;
endmodule
