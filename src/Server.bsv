// This package contains utilities to build coherent masters, to build on of
// those master, the user must provide
// - A Bram interface to read/write the data that the master own
//
// Each of the requests/responses given by the server only contains the first
// message of a burst, and doesn't contains any data, the manager will later
// complete the messages using the Bram is own
//
// Here are some requirements about the ownerchip of the memory in the agent and
// the manager
//
//    Agent
//      ^
//      |
//      v
//   Manager
//      ^
//      | TL
//      v
// Controller
//
// This module define the AcquireFSM, ReleaseFSM and ProbeFSM, it we want
// better performance, we must combine multiple of those module to improve
// the performance by increasing the bandwidth
import Connectable :: *;
import BlockRam :: *;
import TLTypes :: *;
import RegFile :: *;
import Vector :: *;
import Utils :: *;
import Fifo :: *;
import Ehr :: *;

`include "TL.defines"

interface AcquireFSM#(type indexT, `TL_ARGS_DECL);
  method Action setSource(Bit#(sourceW) source);

  method Action acquireBlock(Grow grow, indexT idx, Bit#(addrW) addr);
  method Action acquirePerms(Grow grow, Bit#(addrW) addr);
  method ActionValue#(PermTL) acquireAck();
endinterface

/*
This module manage the refill procedures of a block of ram, it take as argument the
logarithm of the size of the cache blocks it manage, a "block-ram" interface to
manage to write the received data to, and a slave interface to interact with the
coherence controller
*/
module mkAcquireFSM
  #(Bit#(sizeW) logSize, Bram#(Bit#(indexW), Byte#(dataW)) bram, TLSlave#(`TL_ARGS) slave)
  (AcquireFSM#(Bit#(indexW), `TL_ARGS));

  // Current index we use to write in `bram`
  Reg#(Bit#(indexW)) index <- mkReg(?);

  // number of beats to receive before the end of the transfers
  Reg#(Bit#(addrW)) size <- mkReg(?);

  Reg#(Bit#(sourceW)) source <- mkReg(?);
  Reg#(Bool) started <- mkReg(False);

  // true if the module is doing an acquire transfers
  Reg#(Bool) valid <- mkReg(False);

  Reg#(ChannelD#(`TL_ARGS)) channelD <- mkReg(?);
  Reg#(PermTL) perm <- mkReg(?);

  Reg#(Bool) grantStarted <- mkReg(False);

  rule receiveGrantData
    if (
      slave.channelD.first.opcode matches tagged GrantData .p &&&
      slave.channelD.first.source == source
    );
    channelD <= slave.channelD.first;
    slave.channelD.deq();
    perm <= p == N ? N : p == T ? T : B;

    bram.write(index, slave.channelD.first.data);
    grantStarted <= True;

    size <= size - fromInteger(valueOf(dataW));
    index <= index + 1;
  endrule

  rule receiveGrant
    if (
      slave.channelD.first.opcode matches tagged Grant .p &&&
      slave.channelD.first.source == source
    );
    slave.channelD.deq();
    channelD <= slave.channelD.first;
    perm <= p == N ? N : p == T ? T : B;

    grantStarted <= True;

    size <= 0;
    index <= index + 1;
  endrule

  function Action doAcquire(OpcodeA opcode, Bit#(indexW) idx, Bit#(addrW) addr);
    action
      doAssert(
        logSize >= fromInteger(valueOf(TLog#(dataW))),
        "The size of an acquire request must be bigger than the bus width"
      );

      slave.channelA.enq(ChannelA{
        opcode: opcode,
        source: source,
        address: addr,
        size: logSize,
        data: ?,
        mask: ?
      });
      valid <= True;
      index <= idx;
    endaction

  endfunction

  method Action setSource(Bit#(sourceW) src)
    if (!started);
    action
      started <= True;
      source <= src;
    endaction
  endmethod

  method Action acquirePerms(Grow grow, Bit#(addrW) addr)
    if (started && !valid);
    action
      size <= fromInteger(valueOf(dataW));
      doAcquire(AcquirePerms(grow), ?, addr);
    endaction
  endmethod

  method Action acquireBlock(Grow grow, Bit#(indexW) idx, Bit#(addrW) addr)
    if (started && !valid);
    action
      doAcquire(AcquireBlock(grow), idx, addr);
      size <= 1 << logSize;
    endaction
  endmethod

  method ActionValue#(PermTL) acquireAck
    if (started && valid && size == 0);
    grantStarted <= False;
    valid <= False;
    return perm;
  endmethod
endmodule

// A module to send release/probe-ack burst, this module only send the messages,
// and acquire only when it finish: it will not look for the ReleaseAck response
interface BurstFSM#(type indexT, `TL_ARGS_DECL);
  method Action setSource(Bit#(sourceW) source);

  method Action startBurst(OpcodeC opcode, indexT idx, Bit#(addrW) addr, Bit#(sizeW) size);
  method Action finishBurst();
endinterface

module mkBurstFSM
  #(Bram#(Bit#(indexW), Byte#(dataW)) bram, TLSlave#(`TL_ARGS) slave)
  (BurstFSM#(Bit#(indexW), `TL_ARGS));

  Reg#(Bit#(sourceW)) source <- mkReg(?);
  Reg#(Bool) started <- mkReg(False);

  Reg#(ChannelC#(`TL_ARGS)) message <- mkReg(?);

  Bool isRelease = case (message.opcode) matches
    tagged ReleaseData .* : True;
    tagged Release     .* : True;
    default: False;
  endcase;

  Bool releaseAck = slave.channelD.canDeq &&
    slave.channelD.first.opcode == ReleaseAck &&
    slave.channelD.first.source == source;

  // Current index we use to write in `bram`
  Ehr#(2, Bit#(indexW)) index <- mkEhr(?);

  // number of beats to receive before the end of the transfers
  Ehr#(2, Bit#(addrW)) size <- mkEhr(0);

  Ehr#(2, Bool) valid <- mkEhr(False);

  rule releaseStep if (valid[0] && size[0] > 0);
    let data = bram.response();
    bram.deq();

    ChannelC#(`TL_ARGS) msg = message;
    msg.data = data;

    slave.channelC.enq(msg);
    size[0] <= size[0] - fromInteger(valueOf(dataW));
    index[0] <= index[0] + 1;
  endrule

  rule ramRequestRelease
    if (message.opcode matches tagged ReleaseData .* &&& size[1] > 0);
    bram.read(index[1]);
  endrule

  rule ramRequestProbe
    if (message.opcode matches tagged ProbeAckData .* &&& size[1] > 0);
    bram.read(index[1]);
  endrule

  method Action setSource(Bit#(sourceW) src)
    if (!started);
    action
      started <= True;
      source <= src;
    endaction
  endmethod

  method Action startBurst
    (OpcodeC opcode, Bit#(indexW) idx, Bit#(addrW) addr, Bit#(sizeW) logSize)
    if (started && !valid[1]);
    action
      let msg = ChannelC{
        size: logSize,
        opcode: opcode,
        source: source,
        address: addr,
        data: ?
      };

      valid[1] <= True;
      index[1] <= idx;
      message <= msg;

      doAssert(
        logSize >= fromInteger(valueOf(TLog#(dataW))),
        "Burst sender: release and probe size must be bigger than the bus width"
      );

      case (opcode) matches
        tagged ReleaseData .*  : size[1] <= 1 << logSize;
        tagged ProbeAckData .* : size[1] <= 1 << logSize;
        tagged Release .*      : slave.channelC.enq(message);
        tagged ProbeAck .*     : slave.channelC.enq(message);
      endcase
    endaction
  endmethod

  method Action finishBurst()
    if (valid[0] && size[0] == 0 && (!isRelease || releaseAck));
    action
      valid[0] <= False;

      case (message.opcode) matches
        tagged ReleaseData .* : slave.channelD.deq;
        tagged Release     .* : slave.channelD.deq;
        default : noAction;
      endcase
    endaction
  endmethod
endmodule

interface ReleaseFSM#(type indexT, `TL_ARGS_DECL);
  method Action setSource(Bit#(sourceW) source);

  method Action releaseBlock
    (Reduce reduce, indexT idx, Bit#(addrW) addr);
  method Action releaseAck();
endinterface

module mkReleaseFSM
  #(Bit#(sizeW) logSize, Bram#(Bit#(indexW), Byte#(dataW)) bram, TLSlave#(`TL_ARGS) slave)
  (ReleaseFSM#(Bit#(indexW), `TL_ARGS));

  BurstFSM#(Bit#(indexW), `TL_ARGS) burstM <- mkBurstFSM(bram, slave);

  method Action setSource(Bit#(sourceW) source) =
    burstM.setSource(source);

  method Action releaseBlock(Reduce reduce, Bit#(indexW) index, Bit#(addrW) addr) =
    burstM.startBurst(
      reduce == BtoN || reduce == NtoN ? Release(reduce) : ReleaseData(reduce),
      index, addr, logSize
    );

  method Action releaseAck =
    burstM.finishBurst();
endmodule

interface ProbeFSM#(type indexT, `TL_ARGS_DECL);
  method Action setSource(Bit#(sourceW) source);

  method ActionValue#(Tuple2#(Bit#(addrW), PermTL)) probeBlock;

  method Action probeAck(Reduce reduce, indexT idx);

  method Action probeFinish();
endinterface

module mkProbeFSM
  #(Bit#(sizeW) logSize, Bram#(Bit#(indexW), Byte#(dataW)) bram, TLSlave#(`TL_ARGS) slave)
  (ProbeFSM#(Bit#(indexW), `TL_ARGS));

  Reg#(ChannelB#(`TL_ARGS)) message <- mkReg(?);
  Reg#(Bool) needData <- mkReg(?);
  Reg#(PermTL) perms <- mkReg(?);

  Reg#(Bit#(sourceW)) source <- mkReg(?);
  Reg#(Bool) started <- mkReg(False);

  Reg#(Bool) toProbe <- mkReg(False);

  BurstFSM#(Bit#(indexW), `TL_ARGS) burstM <- mkBurstFSM(bram, slave);

  Ehr#(2, Bool) valid <- mkEhr(False);

  rule receiveProbePerms
    if (
      slave.channelB.first.opcode matches tagged ProbePerms .p &&&
      slave.channelB.first.source == source && started && !valid[1]
    );

    let msg = slave.channelB.first;
    perms <= p == T ? T : p == B ? B : N;
    slave.channelB.deq;
    needData <= False;
    valid[1] <= True;
    toProbe <= True;
    message <= msg;

    doAssert(
      logSize == msg.size,
      $format("Probe of size %d only are supported now", logSize)
    );
  endrule

  rule receiveProbeBlock
    if (
      slave.channelB.first.opcode matches tagged ProbeBlock .p &&&
      slave.channelB.first.source == source && started && !valid[1]
    );

    let msg = slave.channelB.first;
    perms <= p == T ? T : p == B ? B : N;
    slave.channelB.deq;
    needData <= True;
    valid[1] <= True;
    toProbe <= True;
    message <= msg;

    doAssert(
      logSize == msg.size,
      $format("Probe of size %d only are supported now", logSize)
    );
  endrule

  method ActionValue#(Tuple2#(Bit#(addrW), PermTL)) probeBlock if (toProbe);
    toProbe <= False;
    return tuple2(message.address, perms);
  endmethod

  method Action probeAck(Reduce reduce, Bit#(indexW) index);
    action
      $display("send burst");
      OpcodeC opcode = (reduce == TtoN || reduce == TtoB) && needData ?
        ProbeAckData(reduce) : ProbeAck(reduce);
      burstM.startBurst(opcode, index, message.address, logSize);
    endaction
  endmethod

  method Action probeFinish;
    action
      valid[0] <= False;
      $display("finish burst");
      burstM.finishBurst();
    endaction
  endmethod

  method Action setSource(Bit#(sourceW) src)
    if (!started);
    action
      burstM.setSource(src);
      started <= True;
      source <= src;
    endaction
  endmethod
endmodule


interface TileLinkServerFSM#(type indexT, `TL_ARGS_DECL);
  method Action setSource(Bit#(sourceW) source);

  method Action acquireBlock(Grow grow, indexT idx, Bit#(addrW) addr);
  method ActionValue#(PermTL) acquireAck();

  method Action releaseBlock(Reduce reduce, indexT idx, Bit#(addrW) addr);
  method Action releaseAck();

  method ActionValue#(Tuple2#(Bit#(addrW), PermTL)) probeBlock;
  method Action probeAck(Reduce reduce, indexT idx);
  method Action probeFinish();
endinterface
