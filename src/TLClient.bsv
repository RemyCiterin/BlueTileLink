import RegFileUtils :: *;
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
  PROBE = 1,

  // Wait for a grant response
  GRANT_WAIT = 2,

  // Send a grant burst
  GRANT_BURST = 3,

  // Receive a put burst
  PUT_BURST = 4,

  // Send a get burst
  GET_BURST = 5
} TLClientState deriving(FShow, Eq, Bits);

// A simple TileLink snoop controller
module mkTileLinkClientFSM#(
    Bit#(sinkW) sink,
    Bit#(sizeW) logSize,
    TLMaster#(`TL_ARGS) master,
    TLSlave#(addrW, dataW, sizeW, sinkW, 0) slave,
    function Bit#(sourceW) repr(Bit#(sourceW) source),
    Vector#(nSource, Bit#(sourceW)) sources
  ) (Empty) provisos (Alias#(Bit#(TAdd#(1, TLog#(nSource))), sourceIdx));

  //Reg#(Bool) waitAccessAck <- mkReg(False);
  Reg#(Bit#(8)) waitAccessAck <- mkReg(0);

  Bit#(sizeW) logBusSize = fromInteger(log2(valueOf(dataW)/8));

  function Bit#(addrW) align(Bit#(addrW) address);
    return address & ~((1 << logSize) - 1);
  endfunction

  Reg#(TLClientState) state <- mkReg(IDLE);

  Reg#(ChannelA#(`TL_ARGS)) channelA <- mkReg(?);
  Reg#(TLPerm) acquirePerm <- mkReg(?);

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

  sourceIdx numSource = fromInteger(valueOf(nSource));

  let metaC <- mkMetaChannelC(master.channelC);
  let channelC = metaC.channel;

  ProbeFSM#(addrW, nSource, `TL_ARGS) probeM <-
    mkProbeFSM(logSize, master.channelB, metaC, sources);

  Bit#(addrW) maxOffset = (1 << (logSize - logBusSize)) - 1;
  RegFile#(Bit#(addrW), Bit#(dataW)) dataBuf <- mkRegFile(0, maxOffset);
  RegFile#(Bit#(addrW), Bit#(1)) epochBuf <- mkRegFileInit(0, maxOffset, 1);
  Reg#(Bit#(1)) epoch <- mkReg(1);

  // Grant state
  Reg#(Bit#(addrW)) grantSize <- mkReg(0);
  Reg#(Bit#(addrW)) grantAddr <- mkReg(0);

  Reg#(Bit#(addrW)) fillAddr <- mkReg(0);
  Reg#(Bit#(addrW)) fillSize <- mkReg(0);

  rule receiveChannelA if (state == IDLE);
    let msg = master.channelA.first;
    epoch <= epoch + 1;

    master.channelA.deq;
    channelA <= msg;

    if (verbose)
      $display("Client: ", fshow(msg));

    grantAddr <= 0;
    grantSize <= 1 << logSize;

    fillAddr <= 0;
    fillSize <= 1 << logSize;

    doAssert(msg.size == logSize, "Invalid channel A request size");

    Bit#(nSource) srcs = -1;
    for (Integer i=0; i < valueOf(nSource); i = i + 1) begin
      if (sources[i] == repr(msg.source)) srcs[i] = 0;
    end

    if (numSource > 1) begin
      Cap cap = permChannelA(msg.opcode) == T ? N : B;
      probeM.start(0, ProbeBlock(cap), align(msg.address), srcs);
      state <= PROBE;
    end else
      state <= GRANT_BURST;
  endrule

  rule probeWrite if (waitAccessAck != maxBound || !metaC.first);
    match {.index, .data, .last} <- probeM.write;

    dataBuf.upd(index, data);
    epochBuf.upd(index, epoch);
    slave.channelA.enq(ChannelA{
      address: channelA.address,
      opcode: PutData,
      data: data,
      size: logSize,
      source: sink,
      mask: -1
    });

    if (metaC.first) waitAccessAck <= waitAccessAck + 1;
  endrule

  (* preempts = "probeWrite,rresponseMEM" *)
  rule rresponseMEM
    if (
      fillSize > 0 &&
      slave.channelD.first.source == sink &&
      slave.channelD.first.opcode == AccessAckData
    );

    dataBuf.upd(fillAddr, slave.channelD.first.data);
    epochBuf.upd(fillAddr, epoch);
    slave.channelD.deq;

    fillSize <= fillSize - fromInteger(valueOf(dataW)/8);
    fillAddr <= fillAddr + 1;
  endrule

  // Ensure that we wait the previous write requests before reading the cache block
  rule toGrant if (state == PROBE && (probeM.receiveData || waitAccessAck == 0));
    state <= GRANT_BURST;
    probeM.finish;

    if (!probeM.receiveData)
      slave.channelA.enq(ChannelA{
        address: channelA.address,
        opcode: GetFull,
        size: logSize,
        source: sink,
        mask: ?,
        data: ?
      });
  endrule

  rule sendGrant if (state == GRANT_BURST &&& epochBuf.sub(grantAddr) == epoch);
    let data = dataBuf.sub(grantAddr);
    grantAddr <= grantAddr + 1;

    Bool last = grantSize == fromInteger(valueOf(dataW)/8);

    master.channelD.enq(ChannelD{
      opcode: GrantData(probeM.exclusive ? T : B),
      source: channelA.source,
      size: channelA.size,
      sink: sink,
      data: data
    });

    if (last) begin
      state <= GRANT_WAIT;
    end

    grantSize <= grantSize - fromInteger(valueOf(dataW)/8);
  endrule

  rule receiveGrantAck
    if (state == GRANT_WAIT && master.channelE.first.sink == sink);

    if (verbose)
      $display("Client: ", fshow(master.channelE.first));

    master.channelE.deq;
    state <= IDLE;
  endrule

  // TODO: ensure that we receive GrantAck before release for a same address
  rule receiveRelease if (
      metaC.channel.first.opcode matches tagged Release .*
    );

    channelC.deq;
    let msg = channelC.first;

    doAssert(msg.size == logSize, "Invalid channel C request size");

    master.channelD.enq(ChannelD{
      opcode: ReleaseAck,
      source: msg.source,
      size: msg.size,
      sink: sink,
      data: ?
    });
  endrule

  // TODO: ensure that we receive GrantAck before release for a same address
  rule receiveReleaseData if (
      channelC.first.opcode matches tagged ReleaseData .* &&&
      (waitAccessAck != maxBound || !metaC.first)
    );

    channelC.deq;
    let msg = channelC.first;
    doAssert(msg.size == logSize, "Invalid channel C request size");

    if (metaC.first) waitAccessAck <= waitAccessAck + 1;
    slave.channelA.enq(ChannelA{
      address: metaC.address,
      opcode: PutData,
      data: msg.data,
      size: logSize,
      source: sink,
      mask: -1
    });

    if (metaC.last) begin
      master.channelD.enq(ChannelD{
        opcode: ReleaseAck,
        source: msg.source,
        size: msg.size,
        sink: sink,
        data: ?
      });
    end
  endrule

  rule sendReleaseAck if (
      slave.channelD.first.source == sink &&
      slave.channelD.first.opcode == AccessAck &&
      waitAccessAck > 0
    );

    slave.channelD.deq;
    waitAccessAck <= waitAccessAck - 1;
  endrule
endmodule

// An interface used by a cache to have a TileLink Client interface, can be
// used as example by a Snoop Filter, a LLC, or just a snoop controller
interface ProbeFSM#(numeric type indexW, numeric type nSource, `TL_ARGS_DECL);
  // Request to the FSM to send a probe signal to a set of sources, and write-back the result
  method Action start(Bit#(indexW) idx, OpcodeB op, Bit#(addrW) addr, Bit#(nSource) owners);

  // Write a received data lane to the response buffer
  method ActionValue#(Tuple3#(Bit#(indexW), Bit#(dataW), Bool)) write;

  // Return if any agent still own the data
  method Bool exclusive;

  // Return if we received some data
  method Bool receiveData;

  // Finish th eprobe sequence
  method Action finish;
endinterface

module mkProbeFSM#(
    Bit#(sizeW) logSize,
    FifoI#(ChannelB#(`TL_ARGS)) channelB,
    MetaChannelC#(`TL_ARGS) metaC,
    Vector#(nSource, Bit#(sourceW)) sources
  ) (ProbeFSM#(indexW, nSource, `TL_ARGS))
  provisos (Alias#(Bit#(TAdd#(1, TLog#(nSource))), sourceIdx));

  let channelC = metaC.channel;
  let message = channelC.first;

  sourceIdx numSource = fromInteger(valueOf(nSource));
  Bit#(sizeW) logBusSize = fromInteger(log2(valueOf(dataW)/8));

  Reg#(Bit#(addrW)) address <- mkReg(?);
  Reg#(Bool) exc <- mkReg(True);

  Reg#(Bit#(nSource)) toSend <- mkReg(0);
  Reg#(Bit#(nSource)) toReceive <- mkReg(0);

  Reg#(OpcodeB) opcode <- mkReg(?);
  Reg#(Bit#(indexW)) index <- mkReg(?);
  Reg#(Bool) hasData <- mkReg(?);

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

    if (verbose)
      $display("Client: ", fshow(message));

    if (reduceTo(reduce) != N) exc <= False;

    channelC.deq;
  endrule

  rule sendProbe if (firstOneFrom(toSend,0) matches tagged Valid .idx);

    let source = sources[idx];
    ChannelB#(`TL_ARGS) msg = ChannelB{
      address: address,
      opcode: opcode,
      source: source,
      size: logSize
    };

    channelB.enq(msg);
    toSend[idx] <= 0;
  endrule

  method ActionValue#(Tuple3#(Bit#(indexW), Bit#(dataW), Bool)) write
    if (message.opcode matches tagged ProbeAckData .reduce &&& message.address == address);

    let idx = findSource(message.source);
    doAssert(toReceive[idx] == 1, "Receive two ProbeAckData from the same source");
    doAssert(!hasData, "Receive a cache block from a Probe request multiple times");
    channelC.deq;

    if (verbose)
      $display("Client: ", fshow(message));

    index <= index + 1;

    if (metaC.last) begin
      if (reduceTo(reduce) != N) exc <= False;
      toReceive[idx] <= 0;
      hasData <= True;
    end

    return tuple3(index, message.data, metaC.last);
  endmethod

  method Action start(Bit#(indexW) idx, OpcodeB op, Bit#(addrW) addr, Bit#(nSource) owners)
    if (!busy);
    action
      exc <= True;
      busy <= True;
      index <= idx;
      opcode <= op;
      address <= addr;
      hasData <= False;
      toSend <= owners;
      toReceive <= owners;
    endaction
  endmethod

  method Action finish if (toReceive == 0 && toSend == 0 && busy);
    action
      busy <= False;
    endaction
  endmethod

  method Bool exclusive = exc;
  method Bool receiveData = hasData;
endmodule
