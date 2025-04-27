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
    return tuple2(index, perm);
  endmethod

  method setSource = acquireM.setSource;

  method Bool canFree = state == Acquire && acquireM.canAcquireAck;

  method Bit#(addrW) address = transaction.next_addr;
  method Bit#(indexW) position = index;
  method Bool active = state != Idle;
endmodule

typedef Bit#(TLog#(num)) Token#(numeric type num);

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
  Bit#(mshr) canFree;
  for (Integer i=0; i < valueOf(mshr); i = i + 1) begin
    canFree[i] = mshrs[i].canFree ? 1 : 0;
  end

  Ehr#(2,Bit#(mshr)) reserved <- mkEhr(0);
  Fifo#(1,Token#(mshr)) reservationQ <- mkPipelineFifo;

  method Action start if (firstOneFrom(reserved[1],0) matches tagged Valid .i);
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

  method ActionValue#(Token#(mshr)) allocate(Transaction#(`TL_ARGS) tr, Bit#(indexW) idx);
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
    if (firstOneFrom(canFree,0) matches tagged Valid .i);
    match {.idx, .perm} <- mshrs[i].free;
    reserved[0][i] <= 0;

    return tuple3(i,idx,perm);
  endmethod

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

interface NBCacheCore
  #(numeric type mshr, numeric type way, type tagT, type indexT, type offsetT, `TL_ARGS_DECL);

  interface TLMaster#(`TL_ARGS) master;

  /*** Stage 1 ***/
  method Action start(indexT index, offsetT offset);

  /*** Stage 2 ***/
  // Return Invalid in case of success, overwise return the MSHR that
  // block the request
  method ActionValue#(Maybe#(Token#(mshr)))
    matching(tagT tag, Bool read, Byte#(dataW) data, Bit#(dataW) mask);

  // Read response
  method ActionValue#(Byte#(dataW)) response;

  // Free a mshr
  method ActionValue#(Token#(mshr)) free;

  /*** Initialisation ***/
  // The first entry is used as a source for release/probe requests
  method Action setSources(Vector#(TAdd#(1,mshr),Bit#(sourceW)) sources);
endinterface

// Invariant: the offset must correspond to the position of a beat in a cache block,
// this configuration can be used to implement banked ram, like even/odd indexes...
typedef struct {
  function Bit#(addrW) encode(Bit#(tagW) tag, Bit#(indexW) index, Bit#(offsetW) offset) encode;
  function Tuple3#(Bit#(tagW),Bit#(indexW),Bit#(offsetW)) decode(Bit#(addrW) tag) decode;
} NBCacheConf#(numeric type tagW, numeric type indexW, numeric type offsetW, `TL_ARGS_DECL);

module mkNBCacheCore#(
    NBCacheConf#(tagW,indexW,offsetW,`TL_ARGS) conf
  )(NBCacheCore#(mshr,way,Bit#(tagW),Bit#(indexW),Bit#(offsetW),`TL_ARGS));

  Vector#(way, Bram#(Bit#(indexW), TLPerm)) permRam <- replicateM(mkBramInit(N));
  Vector#(way, Bram#(Bit#(indexW), Bit#(tagW))) tagRam <- replicateM(mkBram());

  Bit#(sizeW) logSize = fromInteger(valueOf(offsetW) + valueOf(TLog#(dataW)));

  let bram <- mkBramBE();
  Vector#(2, BramBE#(Bit#(TAdd#(TLog#(way), TAdd#(indexW, offsetW))), dataW)) vbram
    <- mkVectorBramBE(bram);

  let vbram0 <- mkBramFromBramBE(vbram[0]);
  MshrFile#(mshr,TAdd#(TLog#(way), TAdd#(offsetW, indexW)), `TL_ARGS) mshr <-
    mkMshrFile(logSize, vbram0);
  let dataRam = vbram[1];

  Reg#(Token#(way)) randomWay <- mkReg(0);

  rule updateRandomWay;
    randomWay <= randomWay + 1;
  endrule

  function Tuple2#(Token#(way),Bit#(indexW))
    decodeIndex(Bit#(TAdd#(TLog#(way), TAdd#(offsetW, indexW))) idx);
    return tuple2(truncateLSB(idx), idx[valueOf(indexW)+valueOf(offsetW)-1:valueOf(offsetW)]);
  endfunction

  Reg#(Bit#(indexW)) index <- mkReg(?);
  Reg#(Bit#(offsetW)) offset <- mkReg(?);
  Reg#(Bit#(addrW)) probeAddr <- mkReg(?);
  Reg#(TLPerm) probePerm <- mkReg(?);

  rule receiveProbe;
    match {.addr, .perm} <- mshr.probeStart();
    match {.tag, .idx, .off} = conf.decode(addr);

    probeAddr <= addr;
    probePerm <= perm;

    for (Integer i=0; i < valueOf(way); i = i + 1) begin
      permRam[i].read(idx);
      tagRam[i].read(idx);
    end
  endrule

  rule matchProbe;
    match {.t, .idx, .off} = conf.decode(probeAddr);
    Bit#(tagW) tag = ?;
    Token#(way) way = ?;
    TLPerm perm = N;

    for (Integer i=0; i < valueOf(way); i = i + 1) begin
      if (tagRam[i].response == t && permRam[i].response > N) begin
        perm = permRam[i].response;
        way = fromInteger(i);
      end

      permRam[i].deq;
      tagRam[i].deq;
    end

    // Same action for a Dirty and Thrunk cache block
    perm = perm == D ? T : perm;

    case (tuple2(perm, probePerm)) matches
      {N, .*} : mshr.probePerms(NtoN);
      {B, T} : mshr.probePerms(BtoB);
      {B, B} : mshr.probePerms(BtoB);
      {T, T} : mshr.probePerms(TtoT);
      {B, N} : begin
        mshr.probePerms(BtoN);
        permRam[way].write(idx, N);
      end
      {T, B} : begin
        mshr.probeBlock(TtoB, {way,idx,0});
        permRam[way].write(idx, B);
      end
      {T, N} : begin
        mshr.probeBlock(TtoN, {way,idx,0});
        permRam[way].write(idx, N);
      end
    endcase
  endrule

  rule finishProbe;
    mshr.probeFinish();
  endrule

  method Action start(Bit#(indexW) idx, Bit#(offsetW) off);
    action
      mshr.start;
      index <= idx;
      offset <= off;

      for (Integer i=0; i < valueof(way); i = i + 1) begin
        permRam[i].read(idx);
        tagRam[i].read(idx);
      end
    endaction
  endmethod

  method ActionValue#(Maybe#(Token#(mshr)))
    matching(Bit#(tagW) t, Bool read, Byte#(dataW) data, Bit#(dataW) mask);

    Token#(way) way = randomWay;

    for (Integer i=0; i < valueof(way); i = i + 1) begin
      if (tagRam[i].response == t && permRam[i].response > N) begin
        way = fromInteger(i);
      end

      permRam[i].deq;
      tagRam[i].deq;
    end

    Bit#(tagW) tag = tagRam[way].response;
    TLPerm perm = tag == t ? permRam[way].response : N;

    Transaction#(`TL_ARGS) tr = Transaction{
      prev_addr: conf.encode(tag,index,0),
      next_addr: conf.encode(t,index,0),
      prev_perm: permRam[way].response,
      next_perm: read ? B : T
    };

    // The request is blocked because a cache miss handling slot
    // already acquire this address, or use the same cache block
    if (mshr.search(conf.encode(t,index,0),{way,index,0}) matches tagged Valid .m) begin
      mshr.stop;
      return Valid(m);
    end else if ((read && perm < B) || (!read && perm < T)) begin
      let m <- mshr.allocate(tr,{way,index,0});
      if (tr.prev_addr != tr.next_addr)
        permRam[way].write(index,N);
      return Valid(m);
    end else begin
      if (read) dataRam.read({way,index,offset});
      else dataRam.write({way,index,offset},data,mask);
      mshr.stop;
      return Invalid;
    end
  endmethod

  method ActionValue#(Byte#(dataW)) response;
    dataRam.deq;
    return dataRam.response;
  endmethod

  method ActionValue#(Token#(mshr)) free;
    match {.m, .idx, .perm} <- mshr.free;
    match {.w,.i} = decodeIndex(idx);
    permRam[w].write(i,perm);
    return m;
  endmethod

  interface master = mshr.master;

  method setSources = mshr.setSources;
endmodule
