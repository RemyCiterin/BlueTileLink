// Drive a BRAM module using TileLink Get and Put requests

import TLTypes :: *;
import BlockRam :: *;
import Fifo :: *;
import Ehr :: *;

export mkTLBram;

`include "TL.defines"

typedef enum {Idle, Write, Read} TLBramState deriving(Bits, FShow, Eq);

module mkTLBram#(
    Bit#(addrW) offset,
    BramBE#(Bit#(addrW), dataW) bram
  ) (TLSlave#(`TL_ARGS));

  Fifo#(2, ChannelA#(`TL_ARGS)) fifoA <- mkFifo;
  Fifo#(2, ChannelD#(`TL_ARGS)) fifoD <- mkFifo;

  TLMaster#(`TL_ARGS) master = interface TLMaster;
    interface channelA = toFifoO(fifoA);
    interface channelB = nullFifoI;
    interface channelC = nullFifoO;
    interface channelD = toFifoI(fifoD);
    interface channelE = nullFifoO;
  endinterface;

  MetaChannelA#(`TL_ARGS) metaA <- mkMetaChannelA(master.channelA);
  let message = metaA.channel.first;

  Bit#(sizeW) logBusSize = fromInteger(log2(valueOf(dataW)/8));
  Integer busSize = valueOf(dataW)/8;

  Reg#(Bit#(sourceW)) msgSource <- mkReg(?);
  Reg#(Bit#(sizeW)) msgSize <- mkReg(?);

  Ehr#(2, TLSize) sizeReg <- mkEhr(0);
  Ehr#(2, Bit#(addrW)) addrReg <- mkEhr(0);

  Ehr#(2, TLBramState) state <- mkEhr(Idle);

  rule readBram if (state[1] == Read);
    bram.read((addrReg[1] - offset) >> logBusSize);
  endrule

  rule startGetFull if (message.opcode == GetFull && state[0] == Idle);
    sizeReg[0] <= 1 << message.size;
    addrReg[0] <= message.address;
    msgSource <= message.source;
    msgSize <= message.size;
    metaA.channel.deq;
    state[0] <= Read;
  endrule

  rule bramResponse if (state[0] == Read);
    Bit#(addrW) addr = addrReg[0];
    TLSize size = sizeReg[0];

    Bool last = fromInteger(busSize) >= size;

    fifoD.enq(ChannelD{
      opcode: AccessAckData,
      data: bram.response,
      source: msgSource,
      size: msgSize,
      sink: ?
    });

    bram.deq;

    state[0] <= last ? Idle : Read;
    sizeReg[0] <= size - fromInteger(busSize);
    addrReg[0] <= addr + fromInteger(busSize);
  endrule

  rule receivePutData
    if (message.opcode == PutData && state[0] != Read);

    bram.write((metaA.address - offset) >> logBusSize, message.data, message.mask);
    metaA.channel.deq;

    state[0] <= metaA.last ? Idle : Write;
    if (metaA.last) begin
      fifoD.enq(ChannelD{
        source: message.source,
        size: message.size,
        opcode: AccessAck,
        sink: ?,
        data: ?
      });
    end
  endrule

  interface channelA = toFifoI(fifoA);
  interface channelB = nullFifoO;
  interface channelC = nullFifoI;
  interface channelD = toFifoO(fifoD);
  interface channelE = nullFifoI;
endmodule
