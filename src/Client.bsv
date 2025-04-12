import Connectable :: *;
import BlockRam :: *;
import CCTypes :: *;
import RegFile :: *;
import Vector :: *;
import Utils :: *;
import Fifo :: *;
import Ehr :: *;

`include "TL.defines"


typedef struct {
  // Infos from the acquire message
  MESI prev;
  MESI next;
  Bit#(addrW) addr;
  Bit#(sizeW) size;
  Bit#(sourceW) source;

  // Status of the probe requests
  Bit#(TLog#(nSource)) next_source;
  Bool send_all;

  // Status of the probe responses
  Bit#(TLog#(nSource)) num_probe_ack;
  Bool receive_all;

  // Is the data forward from another cache
  Bool receive_data;
  Bool exclusive;

  // Status of the forwarding/reading from memory
  Bit#(addrW) pos;
  Bit#(addrW) len;
} AcquireState#(numeric type nSource, numeric type indexW, `CC_ARGS_DECL)
deriving(Bits, FShow, Eq);


module mkSnoopController
  #(
    Bram#(Bit#(addrW), Byte#(dataW)) bram,
    Vector#(nSource, Bit#(sourceW)) sources,
    Bit#(sinkW) sink
  ) (CCSlave#(`CC_ARGS));

  Fifo#(ChannelA#(`CC_ARGS)) fifoA <- mkPipelineFifo;
  Fifo#(ChannelB#(`CC_ARGS)) fifoB <- mkBypassFifo;
  Fifo#(ChannelC#(`CC_ARGS)) fifoC <- mkPipelineFifo;
  Fifo#(ChannelD#(`CC_ARGS)) fifoD <- mkBypassFifo;
  Fifo#(ChannelE#(`CC_ARGS)) fifoE <- mkPipelineFifo;

  Reg#(Bit#(addrW)) releaseAddr <- mkReg(?);
  Reg#(Maybe#(Bit#(addrW))) releaseLength <- mkReg(Invalid);

  Reg#(AcquireState#(nSource, indexW, `CC_ARGS)) state <- mkReg(?);
  Reg#(Bool) valid <- mkReg(False);


  rule receiveRelease if (fifoC.first.opcode matches tagged Release .*);
    fifoD.enq(ChannelD{
      source: fifoC.first.source,
      addr: fifoC.first.addr,
      size: fifoC.first.size,
      opcode: ReleaseAck,
      sink: sink
    });
  endrule

  rule receiveReleaseData if (fifoC.first.opcode matches tagged ReleaseData .*);
    Reg#(addrW) length = 1 << fifoC.first.size;
    Bit#(addrW) address = fifoC.first.addr;
    Bool first = True;

    if (releaseLength matches tagged Valid .l) begin
      address = releaseAddr;
      first = False;
      length = l;
    end

    bram.write(address[valueOf(addrW)-1:valueOf(TLog#(dataW))], fifoC.first.data);

    fifoD.enq(ChannelD{
      source: fifoC.first.source,
      addr: fifoC.first.addr,
      size: fifoC.first.size,
      opcode: ReleaseAck,
      sink: sink
    });

    if (length == 1) begin
      fifoD.enq(ChannelD{
        source: fifoC.first.source,
        addr: fifoC.first.addr,
        size: fifoC.first.size,
        opcode: ReleaseAck,
        sink: sink
      });
    end

    releaseAddr <= first ? address + fromInteger(valueOf(dataW));
    releaseLength <= length == 1 ? Invalid : Valid(length - 1);
  endrule

  rule sendProbe
    if (valid && !state.send_all);
    let source = sources[state.next_source];

    let new_perm = state.next == S ? S : I;

    let msg = ChannelB{
      opcode: tagged Probe new_perm,
      size: state.size,
      addr: state.addr,
      source: source,
    };

    let st = state;
    st.next_source = st.next_source + 1;
    if (state.next_source == fromInteger(valueOf(nSource) - 1))
      st.send_all = True;
    state <= st;

    fifoB.enq(msg);
  endrule

  rule receiveProbeAck if (fifoC.first.opcode matches tagged ProbeAck .perms);
    fifoC.deq();

    let st = state;
    st.num_probe_ack = st.num_probe_ack + 1;
    if (perms.next != I) st.exclusive = False;
    if (state.num_probe_ack == fromInteger(valueOf(nSource) - 1))
      st.receive_all = True;
    state <= st;
  endrule

  rule receiveAcquire
    if (!valid && fifoA.first.opcode matches Acquire .perms);
    let msg = fifoA.first;
    fifoA.deq();

    valid <= True;
    state <= AcquireState{
      source: msg.source,
      prev: perms.prev,
      next: perms.next,
      next_source: 0,
      send_all: False,
      num_probe_ack: 0,
      receive_all: False,
      receive_data: False,
      len: 1 << msg.size,
      exclusive: True,
      size: msg.size,
      addr: msg.addr,
      pos: msg.addr
    };
  endrule

  method channelA = toFifoI(fifoA);
  method channelB = toFifoO(fifoB);
  method channelC = toFifoI(fifoC);
  method channelD = toFifoO(fifoD);
  method channelE = toFifoI(fifoE);
endmodule
