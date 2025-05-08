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
//  ServerFSM
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
import Arbiter :: *;
import RegFile :: *;
import Vector :: *;
import Utils :: *;
import Fifo :: *;
import Ehr :: *;

export AcquireFSM(..);
export ReleaseFSM(..);
export mkAcquireFSM;
export mkReleaseFSM;

`include "TL.defines"

Bool verbose = False;

interface AcquireFSM#(type indexT, `TL_ARGS_DECL);
  method Action setSource(Bit#(sourceW) source);

  method Action acquireBlock(Grow grow, indexT idx, Bit#(addrW) addr);
  method Action acquirePerms(Grow grow, Bit#(addrW) addr);
  method ActionValue#(TLPerm) acquireAck();
  method Bool canAcquireAck;

  // Return if their is currently an acquire request
  method Bool active;

  // Return the address of the current (or last) acquire sequence
  method Bit#(addrW) address;

  // Return if the grant sequence already started
  method Bool grant;

  // Return the requested transition permission of the current (or last) request
  method Grow grow;
endinterface

/*
This module manage the refill procedures of a block of ram, it take as argument the
logarithm of the size of the cache blocks it manage, a "block-ram" interface to
manage to write the received data to, and a slave interface to interact with the
coherence controller
*/
module mkAcquireFSM#(
    Bit#(sizeW) logSize,
    TLSlave#(`TL_ARGS) slave,
    ArbiterClient_IFC arbiter,
    Bram#(Bit#(indexW), Bit#(dataW)) bram
  ) (AcquireFSM#(Bit#(indexW), `TL_ARGS));

  MetaChannelD#(`TL_ARGS) metaD <- mkMetaChannelD(slave.channelD);
  let channelD = metaD.channel;

  // Current index we use to write in `bram`
  Ehr#(2,Bit#(indexW)) index <- mkEhr(?);

  Reg#(Bit#(sourceW)) source <- mkReg(?);
  Reg#(Bool) started <- mkReg(False);

  // true if the module is doing an acquire transfers
  Reg#(Bool) valid <- mkReg(False);

  Reg#(Bool) last <- mkReg(False);

  Reg#(Bit#(sinkW)) sink <- mkReg(?);

  Reg#(TLPerm) perm <- mkReg(?);

  Reg#(Bool) grantStarted <- mkReg(False);
  Reg#(Bit#(addrW)) addrReg <- mkReg(?);
  Reg#(Grow) growReg <- mkReg(?);

  rule arbiterRequest
    if (
      channelD.first.opcode matches tagged GrantData .* &&&
      channelD.first.source == source
    );

    arbiter.request();
  endrule

  rule receiveGrantData
    if (
      channelD.first.opcode matches tagged GrantData .p &&&
      channelD.first.source == source &&
      arbiter.grant
    );
    doAssert(
      channelD.first.size == logSize,
      "Grant responses must have the same size that their associated Acquire request"
    );

    if (verbose)
      $display("Server: %d ", index[0], fshow(channelD.first));

    channelD.deq();
    perm <= p == N ? N : p == T ? T : B;

    bram.write(index[0], channelD.first.data);
    grantStarted <= True;

    index[0] <= index[0] + 1;

    sink <= channelD.first.sink;

    last <= metaD.last;
  endrule

  rule receiveGrant
    if (
      channelD.first.opcode matches tagged Grant .p &&&
      channelD.first.source == source
    );
    doAssert(
      channelD.first.size == logSize,
      "Grant responses must have the same size that their associated Acquire request"
    );

    doAssert(
      !last, "Grant burst must contain only one message, otherwise use GrantData"
    );

    if (verbose)
      $display("Server: ", fshow(channelD.first));

    channelD.deq();
    perm <= p == N ? N : p == T ? T : B;

    grantStarted <= True;

    sink <= channelD.first.sink;

    last <= metaD.last;
  endrule

  function Action doAcquire(OpcodeA opcode, Bit#(indexW) idx, Bit#(addrW) addr);
    action
      doAssert(
        logSize >= fromInteger(log2(valueOf(dataW)/8)),
        "The size of an acquire request must be bigger than the bus width"
      );

      addrReg <= addr;
      slave.channelA.enq(ChannelA{
        opcode: opcode,
        source: source,
        address: addr,
        size: logSize,
        data: ?,
        mask: ?
      });
      index[1] <= idx;
      valid <= True;
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
      doAcquire(AcquirePerms(grow), ?, addr);
      growReg <= grow;
    endaction
  endmethod

  method Action acquireBlock(Grow grow, Bit#(indexW) idx, Bit#(addrW) addr)
    if (started && !valid);
    action
      doAcquire(AcquireBlock(grow), idx, addr);
      growReg <= grow;
    endaction
  endmethod

  method ActionValue#(TLPerm) acquireAck if (last);
    grantStarted <= False;
    valid <= False;
    last <= False;

    slave.channelE.enq(ChannelE{
      opcode: GrantAck,
      sink: sink
    });

    return perm;
  endmethod

  method Bool canAcquireAck = started && valid && last;

  method Bool active = valid;
  method Bit#(addrW) address = addrReg;
  method Bool grant = grantStarted;
  method Grow grow = growReg;
endmodule

// A module to send release/probe-ack burst, this module only send the messages,
// and acquire only when it finish: it will not look for the ReleaseAck response
interface BurstFSM#(type indexT, `TL_ARGS_DECL);
  method Action setSource(Bit#(sourceW) source);

  method Action startBurst(OpcodeC opcode, indexT idx, Bit#(addrW) addr, Bit#(sizeW) size);
  method Action finishBurst();
endinterface

module mkBurstFSM#(
    TLSlave#(`TL_ARGS) slave,
    ArbiterClient_IFC arbiter,
    Bram#(Bit#(indexW), Bit#(dataW)) bram
  ) (BurstFSM#(Bit#(indexW), `TL_ARGS));

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
    size[0] <= size[0] - fromInteger(valueOf(dataW)/8);
    index[0] <= index[0] + 1;
  endrule

  rule arbiterRl1
    if (message.opcode matches tagged ReleaseData .* &&& size[1] > 0);
    arbiter.request;
  endrule

  rule arbiterRl2
    if (message.opcode matches tagged ProbeAckData .* &&& size[1] > 0);
    arbiter.request;
  endrule

  rule ramRequestRelease
    if (message.opcode matches tagged ReleaseData .* &&& size[1] > 0 && arbiter.grant);
    bram.read(index[1]);
  endrule

  rule ramRequestProbe
    if (message.opcode matches tagged ProbeAckData .* &&& size[1] > 0 && arbiter.grant);
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
      ChannelC#(`TL_ARGS) msg = ChannelC{
        opcode: opcode,
        source: source,
        size: logSize,
        address: addr,
        data: ?
      };

      valid[1] <= True;
      index[1] <= idx;
      message <= msg;

      doAssert(
        logSize >= fromInteger(log2(valueOf(dataW)/8)),
        "Burst sender: release and probe size must be bigger than the bus width"
      );

      case (opcode) matches
        tagged ReleaseData .*  : size[1] <= 1 << logSize;
        tagged ProbeAckData .* : size[1] <= 1 << logSize;
        tagged Release .*      : slave.channelC.enq(msg);
        tagged ProbeAck .*     : slave.channelC.enq(msg);
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

  method Bool canProbe;
  method ActionValue#(Tuple2#(Bit#(addrW), TLPerm)) probeStart;
  method Action probeBlock(Reduce reduce, indexT idx);
  method Action probePerms(Reduce reduce);
  method Action probeFinish();

  method Action releaseBlock(Reduce reduce, indexT index, Bit#(addrW) addr);
  method Action releasePerms(Reduce reduce, Bit#(addrW) addr);
  method Action releaseAck();

  // Return if their is currently a transfers
  method Bool active;

  // The address of the current (or last) release sequence
  method Bit#(addrW) address;

  // Return the reduction of the current transfers if it exists
  method Reduce reduce;
endinterface

typedef enum {
  // Wait to receive a source identifier
  INIT,

  // Ready to receive a probe request or an invalidation
  IDLE,

  // Wait for the cache to search for an address
  PROBE_WAIT,

  // Perform a probe burst
  PROBE_BURST,

  // Perform a probe burst
  RELEASE_BURST
} ReleaseState deriving(Bits, FShow, Eq);

module mkReleaseFSM#(
    Bit#(sizeW) logSize,
    TLSlave#(`TL_ARGS) slave,
    ArbiterClient_IFC arbiter,
    Bram#(Bit#(indexW), Bit#(dataW)) bram
  ) (ReleaseFSM#(Bit#(indexW), `TL_ARGS));

  Reg#(ChannelB#(`TL_ARGS)) message <- mkReg(?);
  Reg#(Bool) needData <- mkReg(?);

  Reg#(Bit#(sourceW)) source <- mkReg(?);

  Reg#(Bit#(addrW)) addrReg <- mkReg(?);
  Reg#(Reduce) reduceReg <- mkReg(?);

  BurstFSM#(Bit#(indexW), `TL_ARGS) burstM <- mkBurstFSM(slave, arbiter, bram);

  Ehr#(2, ReleaseState) state <- mkEhr(INIT);

  function ActionValue#(Tuple2#(Bit#(addrW), TLPerm))
    receiveProbe(Cap perm, Bool useData, ChannelB#(`TL_ARGS) msg);
    actionvalue

      doAssert(
        logSize == msg.size,
        $format("Probe of size %d only are supported now", logSize)
      );

      state[1] <= PROBE_WAIT;
      slave.channelB.deq;
      needData <= True;
      message <= msg;

      return tuple2(msg.address, perm == T ? T : perm == B ? B : N);
    endactionvalue
  endfunction

  method Bool canProbe;
    if (slave.channelB.canDeq) begin
      if (slave.channelB.first.source == source && state[1] == IDLE)
        return True;
      else
        return False;
    end else
      return False;
  endmethod

  method ActionValue#(Tuple2#(Bit#(addrW), TLPerm)) probeStart
    if (slave.channelB.first.source == source && state[1] == IDLE);
    let ret = ?;

    if (verbose)
      $display("Server: ", fshow(slave.channelB.first));

    case (slave.channelB.first.opcode) matches
      tagged ProbeBlock .p : ret <- receiveProbe(p, True, slave.channelB.first);
      tagged ProbePerms .p : ret <- receiveProbe(p, False, slave.channelB.first);
      .opcode : begin
        doAssert(
          False, $format("Only probe requests are supported, got: ", fshow(opcode))
        );
      end
    endcase

    return ret;
  endmethod

  method Action probeBlock(Reduce reduce, Bit#(indexW) index)
    if (state[1] == PROBE_WAIT);
    action
      state[1] <= PROBE_BURST;
      doAssert(reduce != NtoN, "ProbeAckData an invalid data");
      OpcodeC opcode = needData ? ProbeAckData(reduce) : ProbeAck(reduce);
      burstM.startBurst(opcode, index, message.address, logSize);
      addrReg <= message.address;
      reduceReg <= reduce;
    endaction
  endmethod

  method Action probePerms(Reduce reduce)
    if (state[1] == PROBE_WAIT);
    action
      state[1] <= PROBE_BURST;
      burstM.startBurst(ProbeAck(reduce), ?, message.address, logSize);
      addrReg <= message.address;
      reduceReg <= reduce;
    endaction
  endmethod

  method Action probeFinish
    if (state[0] == PROBE_BURST);
    action
      state[0] <= IDLE;
      burstM.finishBurst();
    endaction
  endmethod

  method Action setSource(Bit#(sourceW) src)
    if (state[1] == INIT);
    action
      burstM.setSource(src);
      state[1] <= IDLE;
      source <= src;
    endaction
  endmethod

  method Action releaseBlock(Reduce reduce, Bit#(indexW) index, Bit#(addrW) addr)
    if (state[1] == IDLE);
    action
      state[1] <= RELEASE_BURST;
      burstM.startBurst(ReleaseData(reduce), index, addr, logSize);
      reduceReg <= reduce;
      addrReg <= addr;
    endaction
  endmethod

  method Action releasePerms(Reduce reduce, Bit#(addrW) addr)
    if (state[1] == IDLE);
    action
      state[1] <= RELEASE_BURST;
      burstM.startBurst(Release(reduce), ?, addr, logSize);
      reduceReg <= reduce;
      addrReg <= addr;
    endaction
  endmethod

  method Action releaseAck if (state[0] == RELEASE_BURST);
    action
      burstM.finishBurst();
      state[0] <= IDLE;
    endaction
  endmethod

  method active = state[1] != IDLE && state[1] != INIT;
  method reduce = reduceReg;
  method address = addrReg;
endmodule
