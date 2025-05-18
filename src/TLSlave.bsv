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
  GRANT_BURST = 3
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

  sourceIdx numSource = fromInteger(valueOf(nSource));

  let metaA <- mkMetaChannelA(master.channelA);
  let metaC <- mkMetaChannelC(master.channelC);
  let channelC = metaC.channel;

  let grantM <- mkGrantFSM(
    sink, logSize,
    metaA, master.channelB,
    metaC, master.channelD,
    master.channelE,
    slave, repr, sources
  );

  rule startAcquire;
    grantM.start;
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

interface GrantFSM#(`TL_ARGS_DECL);
  // Start to answer to a channel A request, the user must ensure that
  // no other transaction (Acquire, Release...) is using the same address
  method Action start;

  // Return the address and size of the current access
  method Tuple2#(Bit#(addrW),Bit#(sizeW)) access;

  // Return if the FSM is active, in this cas eall the acquire/get/put
  // on the same address are blocked
  method Bool active;

  // Return if the FSM is doing a Grant/GrantAck transfers, in this case
  // all the releases on the same address are blocked
  method Bool grant;
endinterface

typedef enum {
  Idle,
  Probe,
  GrantWait,
  GrantBurst
} GrantState deriving(Bits, FShow, Eq);

module mkGrantFSM#(
    Bit#(sinkW) sink,
    Bit#(sizeW) logSize,
    MetaChannelA#(`TL_ARGS) metaA,
    FifoI#(ChannelB#(`TL_ARGS)) channelB,
    MetaChannelC#(`TL_ARGS) metaC,
    FifoI#(ChannelD#(`TL_ARGS)) channelD,
    FifoO#(ChannelE#(`TL_ARGS)) channelE,
    TLSlave#(addrW, dataW, sizeW, sinkW, 0) slave,
    function Bit#(sourceW) repr(Bit#(sourceW) source),
    Vector#(nSource, Bit#(sourceW)) sources
  ) (GrantFSM#(`TL_ARGS)) provisos (Alias#(Bit#(TAdd#(1, TLog#(nSource))), sourceIdx));

  let channelA = metaA.channel;
  let channelC = metaC.channel;
  Reg#(ChannelA#(`TL_ARGS)) message <- mkReg(?);

  Bit#(sizeW) logBusSize = fromInteger(log2(valueOf(dataW)/8));

  sourceIdx numSource = fromInteger(valueOf(nSource));

  function Bit#(addrW) align(Bit#(addrW) address);
    return address & ~((1 << logSize) - 1);
  endfunction

  ProbeFSM#(addrW, nSource, `TL_ARGS) probeM <-
    mkProbeFSM(logSize, channelB, metaC, sources);

  Bit#(addrW) maxOffset = (1 << (logSize - logBusSize)) - 1;
  RegFile#(Bit#(addrW), Bit#(dataW)) dataBuf <- mkRegFile(0, maxOffset);
  RegFile#(Bit#(addrW), Bit#(1)) epochBuf <- mkRegFileInit(0, maxOffset, 1);
  Reg#(Bit#(1)) epoch <- mkReg(1);

  Reg#(Bit#(addrW)) grantSize <- mkReg(0);
  Reg#(Bit#(addrW)) grantAddr <- mkReg(0);

  Reg#(Bit#(addrW)) fillAddr <- mkReg(0);
  Reg#(Bit#(addrW)) fillSize <- mkReg(0);

  Reg#(TLPerm) perm <- mkReg(?);

  Reg#(GrantState) state <- mkReg(Idle);

  Reg#(Bool) waitAccessAck <- mkReg(False);

  rule probeWrite;
    match {.index, .data, .last} <- probeM.write;

    dataBuf.upd(index, data);
    epochBuf.upd(index, epoch);
    slave.channelA.enq(ChannelA{
      address: message.address,
      opcode: PutData,
      data: data,
      size: logSize,
      source: sink,
      mask: -1
    });

    if (last) waitAccessAck <= True;
  endrule

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

  rule toGrant if (state == Probe);
    state <= GrantBurst;
    probeM.finish;

    if (!probeM.receiveData) begin
      slave.channelA.enq(ChannelA{
        address: message.address,
        opcode: GetFull,
        size: logSize,
        source: sink,
        mask: ?,
        data: ?
      });
    end
  endrule

  rule sendGrant if (state == GrantBurst &&& epochBuf.sub(grantAddr) == epoch);
    let data = dataBuf.sub(grantAddr);
    grantAddr <= grantAddr + 1;

    Bool last = grantSize == fromInteger(valueOf(dataW)/8);

    channelD.enq(ChannelD{
      opcode: GrantData(probeM.exclusive ? T : B),
      source: message.source,
      size: message.size,
      sink: sink,
      data: data
    });

    if (last) begin
      state <= GrantWait;
    end

    grantSize <= grantSize - fromInteger(valueOf(dataW)/8);
  endrule

  rule receiveGrantAckData if (
      slave.channelD.first.source == sink &&
      slave.channelD.first.opcode == AccessAck &&
      waitAccessAck
    );

    slave.channelD.deq;
    waitAccessAck <= False;
  endrule

  rule receiveGrantAck if (
      !waitAccessAck &&
      state == GrantWait &&
      channelE.first.sink == sink
    );

    if (verbose)
      $display("Client: ", fshow(channelE.first));

    channelE.deq;
    state <= Idle;
  endrule

  method Action start if (state == Idle);
    let msg = channelA.first;
    message <= msg;

    channelA.deq;

    // Invalidate all the previous entries in the response buffer
    epoch <= epoch + 1;

    grantAddr <= 0;
    grantSize <= 1 << logSize;

    fillAddr <= 0;
    fillSize <= 1 << logSize;

    if (verbose)
      $display("Client: ", fshow(msg));
    doAssert(msg.size == logSize, "Invalid channel A request size");

    Bit#(nSource) srcs = -1;
    for (Integer i=0; i < valueOf(nSource); i = i + 1) begin
      if (sources[i] == repr(msg.source)) srcs[i] = 0;
    end

    if (numSource > 1) begin
      Cap cap = permChannelA(msg.opcode) == T ? N : B;
      probeM.start(0, ProbeBlock(cap), align(msg.address), srcs);
      state <= Probe;
    end else
      state <= GrantBurst;
  endmethod

  method active = state != Idle;
  method grant = state == GrantWait || state == GrantBurst;
  method access = tuple2(message.address,message.size);
endmodule
