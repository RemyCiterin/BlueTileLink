import BlockRam :: *;
import TLServer :: *;
import TLTypes :: *;
import Vector :: *;
import Utils :: *;
import Fifo :: *;
import Ehr :: *;

import RegFile :: *;
import RegFileUtils :: *;

`include "TL.defines"

typedef struct {
  TLPerm prev_perm;
  TLPerm next_perm;
  Bit#(addrW) prev_addr;
  Bit#(addrW) next_addr;
} Transaction#(`TL_ARGS_DECL) deriving(Bits, FShow, Eq);

interface Mshr
  #(numeric type indexW, `TL_ARGS_DECL);
  // allocate a request (e.g. cache miss)
  method Action allocate(Transaction#(`TL_ARGS) tr, Bit#(indexW) idx);

  method ActionValue#(Tuple2#(Bit#(indexW),TLPerm)) free;

  (* always_ready *)
  method Bool canFree;

  method Action setSource(Bit#(sourceW) source);

  method Bool active;
  method Bit#(addrW) address;
  method Bit#(indexW) position;
endinterface

typedef enum {
  // Ready to receive a new transaction
  Idle,
  // Release a cache block
  Release,
  // Acquire a new cache block
  Acquire
} StateMshr deriving(Bits, FShow, Eq);

module mkMshr#(
    Bit#(sizeW) logSize,
    TLSlave#(`TL_ARGS) slave,
    Bram#(Bit#(indexW), Byte#(dataW)) bram,
    ReleaseFSM#(Bit#(indexW), `TL_ARGS) releaseM
  ) (Mshr#(indexW, `TL_ARGS));

  AcquireFSM#(Bit#(indexW), `TL_ARGS) acquireM <- mkAcquireFSM(logSize, bram, slave);

  Reg#(Bit#(indexW)) index <- mkReg(?);
  Reg#(Transaction#(`TL_ARGS)) transaction <- mkReg(?);
  Reg#(StateMshr) state <- mkReg(Idle);

  rule receiveReleaseAck if (state == Release);
    Grow grow = transaction.prev_perm == B ? NtoB : NtoT;
    acquireM.acquireBlock(grow, index, transaction.next_addr);
    releaseM.releaseAck();
    state <= Acquire;
  endrule

  method Action allocate(Transaction#(`TL_ARGS) tr, Bit#(indexW) idx);
    action
      if (tr.next_perm == D) tr.next_perm = T;

      if (state == Idle) begin
        transaction <= tr;
        index <= idx;

        if (tr.next_addr == tr.prev_addr || tr.prev_perm == N) begin
          Grow grow = tr.next_perm == B ? NtoB : NtoT;
          acquireM.acquireBlock(grow, idx, tr.next_addr);
          state <= Acquire;
        end else begin
          Reduce reduce = tr.prev_perm == B ? BtoN : TtoN;
          releaseM.releaseBlock(reduce, idx, tr.prev_addr);
          state <= Release;
        end

      end else begin
        doAssert(tr.next_addr == transaction.next_addr, "Wrong MSHR for this address");
      end
    endaction
  endmethod

  method ActionValue#(Tuple2#(Bit#(indexW),TLPerm)) free if (state == Acquire);
    let perm <- acquireM.acquireAck();
    state <= Idle;

    return tuple2(index, perm);
  endmethod

  method setSource = acquireM.setSource;

  method Bool canFree = state == Acquire && acquireM.canAcquireAck;

  method Bit#(addrW) address = transaction.next_addr;
  method Bit#(indexW) position = index;
  method Bool active = state != Idle;
endmodule

interface MshrFile
  #(numeric type mshr, numeric type indexW, `TL_ARGS_DECL);
  /*** Memory interface ***/
  interface TLMaster#(`TL_ARGS) master;

  /*** Stage 1 ***/
  // Start a cache request
  method Action start;

  /*** Stage 2 ***/
  // Stop a cache request without reading from memory (e.g. cache miss)
  method Action stop;

  // Search if an Mshr match the current request address
  method Maybe#(Token#(mshr)) search(Bit#(addrW) address, Bit#(indexW) index);

  // Allocate a request (e.g. cache miss)
  method ActionValue#(Token#(mshr)) allocate(Transaction#(`TL_ARGS) tr, Bit#(indexW) idx);

  /*** Stage 3 ***/
  // Inform the core that a transaction finish
  method ActionValue#(Tuple3#(Token#(mshr),Bit#(indexW),TLPerm)) free;

  // Return if a free is possible
  (* always_ready *)
  method Bool canFree;

  /*** Initialisation ***/
  // The first entry is used as a source for release/probe requests
  method Action setSources(Vector#(TAdd#(1,mshr),Bit#(sourceW)) sources);

  /*** Probe interface ***/
  method ActionValue#(Tuple2#(Bit#(addrW), TLPerm)) probeStart;
  method Action probeBlock(Reduce reduce, Bit#(indexW) idx);
  method Action probePerms(Reduce reduce);
  method Action probeFinish();
endinterface

module mkMshrFile#(
    Bit#(sizeW) logSize,
    Bram#(Bit#(indexW), Byte#(dataW)) bram
  ) (MshrFile#(mshr,indexW,`TL_ARGS));

  Fifo#(mshr, ChannelA#(`TL_ARGS)) fifoA <- mkFifo;
  Fifo#(2, ChannelB#(`TL_ARGS)) fifoB <- mkFifo;
  Fifo#(2, ChannelC#(`TL_ARGS)) fifoC <- mkFifo;
  Fifo#(2, ChannelD#(`TL_ARGS)) fifoD <- mkFifo;
  Fifo#(2, ChannelE#(`TL_ARGS)) fifoE <- mkFifo;

  TLSlave#(`TL_ARGS) slave = interface TLSlave;
    interface channelA = toFifoI(fifoA);
    interface channelB = toFifoO(fifoB);
    interface channelC = toFifoI(fifoC);
    interface channelD = toFifoO(fifoD);
    interface channelE = toFifoI(fifoE);
  endinterface;

  ReleaseFSM#(Bit#(indexW),`TL_ARGS) releaseM <- mkReleaseFSM(logSize, bram,slave);
  Vector#(mshr, Mshr#(indexW,`TL_ARGS)) mshrs <- replicateM(mkMshr(logSize, slave, bram, releaseM));

  // Static scheduler to free any ready Mshr
  Bit#(mshr) freeMask;
  for (Integer i=0; i < valueOf(mshr); i = i + 1) begin
    freeMask[i] = mshrs[i].canFree ? 1 : 0;
  end

  Ehr#(2,Bit#(mshr)) reserved <- mkEhr(0);
  Fifo#(1,Token#(mshr)) reservationQ <- mkPipelineFifo;

  method Action start if (firstOneFrom(~reserved[1],0) matches tagged Valid .i);
    action
      reserved[1][i] <= 1;
      reservationQ.enq(i);
    endaction
  endmethod

  method Action stop;
    action
      reserved[0][reservationQ.first] <= 0;
      reservationQ.deq;
    endaction
  endmethod

  method ActionValue#(Token#(mshr)) allocate(Transaction#(`TL_ARGS) tr, Bit#(indexW) idx)
    if (!releaseM.active);
    let i = reservationQ.first;
    reservationQ.deq;

    mshrs[i].allocate(tr, idx);

    return i;
  endmethod

  method Maybe#(Token#(mshr)) search(Bit#(addrW) address, Bit#(indexW) index);
    Maybe#(Token#(mshr)) result = Invalid;

    for (Integer i=0; i < valueOf(mshr); i = i + 1) begin
      if (mshrs[i].active && (mshrs[i].address == address || mshrs[i].position == index))
        result = Valid(fromInteger(i));
    end

    return result;
  endmethod

  method ActionValue#(Tuple3#(Token#(mshr),Bit#(indexW),TLPerm)) free
    if (firstOneFrom(freeMask,0) matches tagged Valid .i);
    match {.idx, .perm} <- mshrs[i].free;
    reserved[0][i] <= 0;

    return tuple3(i,idx,perm);
  endmethod

  method canFree = freeMask != 0;

  interface TLMaster master;
    interface channelA = toFifoO(fifoA);
    interface channelB = toFifoI(fifoB);
    interface channelC = toFifoO(fifoC);
    interface channelD = toFifoI(fifoD);
    interface channelE = toFifoO(fifoE);
  endinterface

  method probeStart = releaseM.probeStart;
  method probeBlock = releaseM.probeBlock;
  method probePerms = releaseM.probePerms;
  method probeFinish = releaseM.probeFinish;

  method Action setSources(Vector#(TAdd#(1,mshr),Bit#(sourceW)) sources);
    action
      releaseM.setSource(sources[0]);
      for (Integer i=0; i < valueOf(mshr); i = i + 1) begin
        mshrs[i].setSource(sources[i+1]);
      end
    endaction
  endmethod
endmodule
