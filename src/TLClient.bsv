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

export mkTileLinkClientFSM;

Bool verbose = False;

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

interface AcquireBuffer#(`TL_ARGS_DECL);
  // Write into the buffer a beat from a cache due to a probe request
  method Action enqProbe(Byte#(dataW) value);

  // Write into the buffer a beat from memory
  method Action enqMem(Byte#(dataW) value);

  // Read one word from the buffer
  method ActionValue#(Byte#(dataW)) deq;

  // Start a new transaction
  method Action start;
endinterface

module mkAcquireBuffer#(Bit#(sizeW) logSize) (AcquireBuffer#(`TL_ARGS));
  Bit#(sizeW) logDataW = fromInteger(valueOf(TLog#(dataW)));
  Bit#(addrW) maxOffset = (1 << (logSize - logDataW)) - 1;

  RegFile#(Bit#(addrW), Maybe#(Byte#(dataW))) buffer <- mkRegFile(0, maxOffset);

  function Bit#(addrW) next(Bit#(addrW) idx) = idx == maxOffset ? 0 : idx + 1;
  Reg#(Maybe#(Bit#(addrW))) memHead <- mkReg(Invalid);
  Reg#(Bit#(addrW)) probeHead <- mkReg(0);
  Reg#(Bit#(addrW)) deqHead <- mkReg(0);

  Reg#(Bool) isInit <- mkReg(False);

  rule init if (!isInit);
    buffer.upd(deqHead, Invalid);
    deqHead <= next(deqHead);

    if (deqHead == maxOffset)
      isInit <= True;
  endrule

  method Action enqProbe(Byte#(dataW) value) if (isInit);
    action
      buffer.upd(probeHead, Valid(value));
      probeHead <= next(probeHead);
    endaction
  endmethod

  method Action enqMem(Byte#(dataW) value)
    if (isInit &&& memHead matches tagged Valid .head);
    action
      if (buffer.sub(head) == Invalid && deqHead <= head)
        buffer.upd(head, Valid(value));

      memHead <= head == maxOffset ? Invalid : Valid(head+1);
    endaction
  endmethod

  method ActionValue#(Byte#(dataW)) deq
    if (buffer.sub(deqHead) matches tagged Valid .data);
    buffer.upd(deqHead, Invalid);
    deqHead <= next(deqHead);
    return data;
  endmethod

  method Action start if (memHead == Invalid);
    action
      doAssert(probeHead == 0, "probe head must be 0");
      doAssert(deqHead == 0, "deq head must be 0");
      memHead <= Valid(0);
    endaction
  endmethod
endmodule

// A TileLink snoop controller
module mkTileLinkClientFSM#(
    Bit#(sinkW) sink,
    Bit#(sizeW) logSize,
    TLMaster#(`TL_ARGS) master,
    TLSlave#(addrW, dataW, sizeW, sinkW, 0) slave,
    Vector#(nSource, Bit#(sourceW)) sources
  ) (Empty) provisos (Alias#(Bit#(TAdd#(1, TLog#(nSource))), sourceIdx));

  Reg#(Bool) waitAccessAck <- mkReg(False);

  Bit#(sizeW) logDataW = fromInteger(valueOf(TLog#(dataW)));

  Reg#(TLClientState) state <- mkReg(IDLE);
  Reg#(TLClientState) nextState <- mkReg(IDLE);

  Reg#(ChannelA#(`TL_ARGS)) channelA <- mkReg(?);
  Reg#(TLPerm) acquirePerm <- mkReg(?);

  AcquireBuffer#(`TL_ARGS) buffer <- mkAcquireBuffer(logSize);

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
  Reg#(TLSize) releaseSize <- mkReg(0);
  Reg#(Bit#(addrW)) releaseAddr <- mkReg(0);

  // Probe state
  sourceIdx numSource = fromInteger(valueOf(nSource));
  Reg#(Bit#(addrW)) probeAddr <- mkReg(0);
  Reg#(sourceIdx) probeCount <- mkReg(?);
  Reg#(sourceIdx) probeNext <- mkReg(?);
  Reg#(TLSize) probeSize <- mkReg(0);
  Reg#(Bool) exclusive <- mkReg(?);

  // Grant state
  Reg#(Bit#(addrW)) grantSize <- mkReg(0);

  Ehr#(2, Bit#(addrW)) fillAddr <- mkEhr(0);
  Ehr#(2, Bit#(addrW)) fillSize <- mkEhr(0);
  Ehr#(2, Bool) needFill <- mkEhr(False);

  rule receiveChannelA if (state == IDLE && !waitAccessAck);
    state <= 1 >= numSource ? GRANT_BURST : PROBE_WAIT;
    channelA <= master.channelA.first;
    probeCount <= numSource - 1;
    grantSize <= 1 << logSize;
    master.channelA.deq;
    exclusive <= True;
    probeNext <= 0;

    if (verbose)
      $display("Client: ", fshow(master.channelA.first));

    buffer.start();
    fillAddr[0] <= master.channelA.first.address;
    fillSize[0] <= 1 << logSize;
    needFill[0] <= True;

    slave.channelA.enq(ChannelA{
      address: master.channelA.first.address,
      opcode: GetFull,
      size: logSize,
      source: sink,
      mask: ?,
      data: ?
    });

    doAssert(master.channelA.first.size == logSize, "Invalid channel A request size");
  endrule

  rule sendProbe if (state == PROBE_WAIT && probeNext < numSource);
    Cap cap = permChannelA(channelA.opcode) == T ? N : B;

    let source = sources[probeNext];
    if (source != channelA.source)
      master.channelB.enq(ChannelB{
        address: channelA.address,
        opcode: ProbeBlock(cap),
        size: channelA.size,
        source: source
      });

    probeNext <= probeNext + 1;
  endrule

  rule receiveProbeAck if (
      state == PROBE_WAIT &&&
      master.channelC.first.opcode matches tagged ProbeAck .reduce
    );

    if (verbose)
      $display("Client: ", fshow(master.channelC.first));

    master.channelC.deq;
    doAssert(probeCount != 0, "Receive more ProbeAck than expected");

    if (reduceTo(reduce) != N && master.channelC.first.source != channelA.source)
      exclusive <= False;

    probeCount <= probeCount - 1;

    if (probeCount == 1) state <= GRANT_BURST;
  endrule

  rule receiveProbeAckData if (
      (state == PROBE_WAIT || state == PROBE_BURST) &&&
      master.channelC.first.opcode matches tagged ProbeAckData .reduce &&&
      (!waitAccessAck || state == PROBE_BURST)
    );

    let msg = master.channelC.first;

    if (verbose)
      $display("Client: ", fshow(msg));

    doAssert(msg.size == logSize, "Receive ProbeAckData of an incorrcet size");
    TLSize size = state == PROBE_BURST ? probeSize : 1 << channelA.size;
    Bit#(addrW) addr = state == PROBE_BURST ? probeAddr : channelA.address;
    Bool first = state != PROBE_BURST;

    if (first) waitAccessAck <= True;
    slave.channelA.enq(ChannelA{
      address: msg.address,
      opcode: PutData,
      data: msg.data,
      size: logSize,
      source: sink,
      mask: -1
    });
    buffer.enqProbe(msg.data);

    master.channelC.deq;
    if (reduceTo(reduce) != N && msg.source != channelA.source)
      exclusive <= False;

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

  (* preempts = "receiveProbeAckData,rresponseMEM" *)
  rule rresponseMEM
    if (
      needFill[0] && fillSize[0] > 0 &&
      slave.channelD.first.source == sink &&
      slave.channelD.first.opcode == AccessAckData
    );
    buffer.enqMem(slave.channelD.first.data);
    slave.channelD.deq;

    fillSize[0] <= fillSize[0] - fromInteger(valueOf(dataW));
    fillAddr[0] <= fillAddr[0] + fromInteger(valueOf(dataW));

    if (fillSize[0] == fromInteger(valueOf(dataW))) begin
      needFill[0] <= False;
    end
  endrule

  rule sendGrant if (state == GRANT_BURST);
    let data <- buffer.deq;

    Bool last = grantSize == fromInteger(valueOf(dataW));

    master.channelD.enq(ChannelD{
      opcode: GrantData(exclusive ? T : B),
      source: channelA.source,
      size: channelA.size,
      sink: sink,
      data: data
    });

    if (last) begin
      state <= GRANT_WAIT;
    end

    grantSize <= grantSize - fromInteger(valueOf(dataW));
  endrule

  rule receiveGrantAck
    if (state == GRANT_WAIT && !needFill[1] && master.channelE.first.sink == sink);
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
      master.channelC.first.opcode matches tagged ReleaseData .* &&&
      (!waitAccessAck || state == RELEASE_BURST)
    );

    master.channelC.deq;
    let msg = master.channelC.first;
    TLSize size = state == RELEASE_BURST ? releaseSize : 1 << msg.size;
    Bit#(addrW) addr = state == RELEASE_BURST ? releaseAddr : msg.address;
    Bool first = state != RELEASE_BURST;

    doAssert(msg.size == logSize, "Invalid channel C request size");

    if (first) waitAccessAck <= True;
    slave.channelA.enq(ChannelA{
      opcode: PutData,
      data: msg.data,
      address: addr,
      size: logSize,
      source: sink,
      mask: -1
    });

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

  rule sendReleaseAck if (
      slave.channelD.first.source == sink &&
      slave.channelD.first.opcode == AccessAck &&
      waitAccessAck
    );

    slave.channelD.deq;
    waitAccessAck <= False;
  endrule
endmodule

// An interface used by a cache to have a TileLink Client interface, can be
// used as example by a Snoop Filter, a LLC, or just a snoop controller
interface ProbeFSM#(numeric type indexW, numeric type nSource, `TL_ARGS_DECL);
  // Request to the FSM to send a probe signal to a set of sources, and write-back the result
  method Action start(Bit#(indexW) index, OpcodeB opcode, Bit#(addrW) address, Bit#(nSource) owners);

  // Return if any agent still own the data
  method Bool exclusive;

  // Finish th eprobe sequence
  method Action finish;
endinterface

module mkProbeFSM#(
    Bit#(sizeW) logSize,
    TLMaster#(`TL_ARGS) master,
    Vector#(nSource, Bit#(sourceW)) sources,
    Bram#(Bit#(indexW), Byte#(dataW)) bram
  ) (ProbeFSM#(indexW, nSource, `TL_ARGS))
  provisos (Alias#(Bit#(TAdd#(1, TLog#(nSource))), sourceIdx));

  let metaC <- mkMetaChannelC(master.channelC);
  let channelC = metaC.channel;
  let message = channelC.first;

  sourceIdx numSource = fromInteger(valueOf(nSource));
  Bit#(sizeW) logDataW = fromInteger(valueOf(TLog#(dataW)));

  Reg#(Bit#(addrW)) address <- mkReg(?);
  Reg#(sourceIdx) next <- mkReg(?);
  Reg#(Bool) exc <- mkReg(?);

  Reg#(Bit#(nSource)) toSend <- mkReg(0);
  Reg#(Bit#(nSource)) toReceive <- mkReg(0);

  Reg#(OpcodeB) opcode <- mkReg(?);
  Reg#(Bit#(indexW)) index <- mkReg(?);

  Reg#(Bool) busy <- mkReg(False);

  function sourceIdx findSource(Bit#(sourceW) source);
    sourceIdx idx = ?;

    for (Integer i=0; i < valueOf(nSource); i = i + 1) begin
      if (source == sources[i]) idx = fromInteger(i);
    end

    return idx;
  endfunction

  rule receiveProbeAck
    if (message.opcode matches tagged ProbeAck .reduce &&& message.address == address);

    let idx = findSource(message.source);
    doAssert(toReceive[idx] == 1, "Receive two ProbeAck from the same source");
    toReceive[idx] <= 0;

    if (reduceTo(reduce) != N) exc <= False;

    channelC.deq;
  endrule

  rule receiveProbeAckData
    if (message.opcode matches tagged ProbeAckData .reduce &&& message.address == address);

    let idx = findSource(message.source);
    doAssert(toReceive[idx] == 1, "Receive two ProbeAck from the same source");
    channelC.deq;

    bram.write(index, message.data);
    index <= index + 1;

    if (metaC.last) begin
      if (reduceTo(reduce) != N) exc <= False;
      toReceive[idx] <= 0;
    end
  endrule

  rule sendProbe if (firstOneFrom(toSend,0) matches tagged Valid .idx);
    let source = sources[idx];
    master.channelB.enq(ChannelB{
      address: address,
      opcode: opcode,
      source: source,
      size: logSize
    });

    toSend[idx] <= 0;
  endrule

  method Action start(Bit#(indexW) idx, OpcodeB op, Bit#(addrW) addr, Bit#(nSource) owners);
    action
      next <= 0;
      exc <= False;
      busy <= True;
      index <= idx;
      opcode <= op;
      address <= addr;
      toSend <= owners;
      toReceive <= owners;
    endaction
  endmethod

  method Action finish if (toReceive == 0 && busy);
    action
      busy <= False;
    endaction
  endmethod

  method Bool exclusive = exc;
endmodule
