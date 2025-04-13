import Connectable :: *;
import BlockRam :: *;
import TLTypes :: *;
import RegFile :: *;
import Vector :: *;
import Utils :: *;
import AXI4 :: *;
import Fifo :: *;
import Ehr :: *;

`include "TL.defines"

typedef enum {
  // Ready to receive a new acquire request
  IDLE = 0,

  // Send probe requests, and wait for response
  PROBE_WAIT = 1,

  // Wait for a grant response
  GRANT_WAIT = 2,

  // Receive a probe burst
  PROBE_BURST = 3,

  // Send a grant burst
  GRANT_BURST = 4,

  // Receive a put burst
  PUT_BURST = 5,

  // Send a get burst
  GET_BURST = 6,

  // Receive a release burst
  RELEASE_BURST = 7
} TLClientState deriving(FShow, Eq, Bits);

// Receive put, release, or probe burst
interface ReceiveBurstFSM#(numeric type nSource, `TL_ARGS_DECL);
  // Must receive `nSource` ProbeAck or ProbeAckData messages
  // it it receive a ProbeAckData it perform the grant directly
  method Action probeAck(Grow grow, Bit#(addrW) addr);
  // Return if one of the probe response was ProbeAckData,
  method ActionValue#(Bool) receiveProbeAck;

  method Action put();
  method Action putAck();
endinterface


module mkTileLinkClientFSM#(
    Bit#(sinkW) sink,
    Bit#(sizeW) logSize,
    TLMaster#(`TL_ARGS) master,
    Bram#(Bit#(addrW), Byte#(dataW)) bram,
    Vector#(nSource, Bit#(sourceW)) sources
  ) (Empty) provisos (Alias#(Bit#(TAdd#(1, TLog#(nSource))), sourceIdx));

  Bit#(sizeW) logDataW = fromInteger(valueOf(TLog#(dataW)));

  Reg#(TLClientState) state <- mkReg(IDLE);
  Reg#(TLClientState) nextState <- mkReg(IDLE);

  Reg#(ChannelA#(`TL_ARGS)) channelA <- mkReg(?);

  function Action startGrant();
    action
      state <= case (channelA.opcode) matches
        tagged AcquireBlock .* : GRANT_BURST;
        tagged AcquirePerms .* : GRANT_BURST;
        PutData : PUT_BURST;
        GetFull : GET_BURST;
      endcase;
    endaction
  endfunction

  // Release state
  Reg#(Bit#(addrW)) releaseSize <- mkReg(0);
  Reg#(Bit#(addrW)) releaseAddr <- mkReg(0);

  // Probe state
  sourceIdx numSource = fromInteger(valueOf(nSource));
  Reg#(Bit#(addrW)) probeAddr <- mkReg(0);
  Reg#(Bit#(addrW)) probeSize <- mkReg(0);
  Reg#(sourceIdx) probeCount <- mkReg(?);
  Reg#(sourceIdx) probeNext <- mkReg(?);

  // Grant state
  Ehr#(2, Bit#(addrW)) grantAddr <- mkEhr(0);
  Ehr#(2, Bit#(addrW)) grantSize <- mkEhr(0);

  rule receiveChannelA if (state == IDLE);
    $display("Receive channel A request");
    grantAddr[0] <= master.channelA.first.address;
    channelA <= master.channelA.first;
    grantSize[0] <= 1 << logSize;
    probeCount <= numSource;
    master.channelA.deq;
    state <= PROBE_WAIT;
    probeNext <= 0;

    doAssert(master.channelA.first.size == logSize, "Invalid channel C request size");
  endrule

  rule sendProbe if (state == PROBE_WAIT && probeNext < numSource);
    let source = sources[probeNext];
    master.channelB.enq(ChannelB{
      address: channelA.address,
      opcode: ProbeBlock(N),
      size: channelA.size,
      source: source
    });

    probeNext <= probeNext + 1;
    $display("Send Probe request to %d", source);
  endrule

  rule receiveProbeAck if (
      state == PROBE_WAIT &&&
      master.channelC.first.opcode matches tagged ProbeAck .*
    );

    master.channelC.deq;
    doAssert(probeCount == 0, "Receive more ProbeAck than expected");
    probeCount <= probeCount - 1;

    $display("Receive ProbeAck from %d", master.channelC.first.source);

    if (probeCount == 1) state <= GRANT_BURST;
  endrule

  rule receiveProbeAckData if (
      (state == PROBE_WAIT || state == PROBE_BURST) &&&
      master.channelC.first.opcode matches tagged ProbeAckData .*
    );

    doAssert(master.channelC.first.size == logSize, "Receive ProbeAckData of an incorrcet size");
    Bit#(addrW) size = state == PROBE_BURST ? probeSize : 1 << channelA.size;
    Bit#(addrW) addr = state == PROBE_BURST ? probeAddr : channelA.address;
    Bool first = state != PROBE_BURST;

    bram.write(addr >> logDataW, master.channelC.first.data);

    $display("Receive ProbeAckData from %d", master.channelC.first.source);

    master.channelC.deq;
    doAssert(probeCount != 0, "Receive more ProbeAckData than expected");

    probeSize <= size - fromInteger(valueOf(dataW));
    probeAddr <= addr + fromInteger(valueOf(dataW));
    Bool last = size == fromInteger(valueOf(dataW));

    if (last) begin
      state <= probeCount == 1 ? GRANT_BURST : PROBE_WAIT;
      probeCount <= probeCount - 1;
    end else begin
      state <= PROBE_BURST;
    end
  endrule

  rule readRam if (state == GRANT_BURST && grantSize[1] > 0);
    bram.read(grantAddr[1] >> logDataW);
  endrule

  rule sendGrant if (state == GRANT_BURST);
    let data = bram.response;
    bram.deq;

    master.channelD.enq(ChannelD{
      source: channelA.source,
      size: channelA.size,
      opcode: GrantData(T),
      sink: sink,
      data: data
    });

    grantSize[0] <= grantSize[0] - fromInteger(valueOf(dataW));
    grantAddr[0] <= grantAddr[0] + fromInteger(valueOf(dataW));

    if (grantSize[0] == fromInteger(valueOf(dataW))) begin
      state <= GRANT_WAIT;
    end
  endrule

  rule receiveGrantAck
    if (state == GRANT_WAIT && master.channelE.first.sink == sink);
    master.channelE.deq;
    state <= IDLE;
  endrule

  rule receiveRelease if (
      (state == IDLE || state == PROBE_WAIT) &&&
      master.channelC.first.opcode matches tagged Release .*
    );

    master.channelC.deq;
    let msg = master.channelC.first;

    doAssert(msg.size == logSize, "Invalid channel C request size");

    master.channelD.enq(ChannelD{
      opcode: ReleaseAck,
      source: msg.source,
      size: msg.size,
      sink: sink,
      data: ?
    });
  endrule

  rule receiveReleaseData if (
      (state == IDLE || state == PROBE_WAIT || state == RELEASE_BURST) &&&
      master.channelC.first.opcode matches tagged ReleaseData .*
    );

    master.channelC.deq;
    let msg = master.channelC.first;
    Bit#(addrW) size = state == RELEASE_BURST ? releaseSize : 1 << msg.size;
    Bit#(addrW) addr = state == RELEASE_BURST ? releaseAddr : msg.address;
    Bool first = state != RELEASE_BURST;

    doAssert(msg.size == logSize, "Invalid channel C request size");

    bram.write(addr >> logDataW, msg.data);

    releaseAddr <= addr + fromInteger(valueOf(dataW));
    releaseSize <= size - fromInteger(valueOf(dataW));
    Bool last = size == fromInteger(valueOf(dataW));

    if (last) begin
      master.channelD.enq(ChannelD{
        opcode: ReleaseAck,
        source: msg.source,
        size: msg.size,
        sink: sink,
        data: ?
      });
    end

    if (first && !last) begin
      state <= RELEASE_BURST;
      nextState <= state;
    end else if (last && !first) begin
      state <= nextState;
    end
  endrule
endmodule
