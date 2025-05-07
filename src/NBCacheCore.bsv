import BlockRam :: *;
import TLServer :: *;
import TLTypes :: *;
import Arbiter :: *;
import Vector :: *;
import Utils :: *;
import MSHR :: *;
import Fifo :: *;
import PLRU :: *;
import Ehr :: *;

export NBCacheCore(..);
export NBCacheConf(..);
export NBCacheAck(..);
export mkNBCacheCore;

`include "TL.defines"

typedef union tagged {
  void Load;

  struct {
    Bit#(dataW) mask;
    Byte#(dataW) data;
  } Store;
} NBCacheOp#(`TL_ARGS_DECL) deriving(Bits, FShow, Eq);

typedef union tagged {
  // The request is a success
  void Success;

  // The request is blocked, we can re-fire the request as soon as a mshr is free
  void Blocked;

  // The request is blocked, we can re-fire the request as soon as the mshr is free
  Token#(mshr) BlockedBy;
} NBCacheAck#(numeric type mshr) deriving(Bits, FShow, Eq);

interface NBCacheCore
  #(numeric type mshr, numeric type way, type tagT, type indexT, type offsetT, `TL_ARGS_DECL);

  interface TLMaster#(`TL_ARGS) master;

  /*** Stage 1 ***/
  method Action
    lookup(indexT index, offsetT offset, Bool read, Byte#(dataW) data, Bit#(dataW) mask);

  /*** Stage 2 ***/
  // Return Invalid in case of success, overwise return the MSHR that
  // block the request
  method ActionValue#(NBCacheAck#(mshr)) matching(tagT tag);

  // Stop a request (e.g. TLB miss)
  method Action abort;

  // Read response
  method ActionValue#(Byte#(dataW)) response;

  // Free a mshr
  method ActionValue#(Token#(mshr)) free;

  /*** Initialisation ***/
  // The first entry is used as a source for release/probe requests
  method Action setSources(Vector#(TAdd#(1,mshr),Bit#(sourceW)) sources);

  /*** Inform host CPU that we evict a cache block ***/
  interface FifoO#(Bit#(addrW)) evict;
endinterface

// Invariant: the offset must correspond to the position of a beat in a cache block,
// this configuration can be used to implement banked ram, like even/odd indexes...
typedef struct {
  function Bit#(addrW) encode(Bit#(tagW) tag, Bit#(indexW) index, Bit#(offsetW) offset) encode;
  function Tuple3#(Bit#(tagW),Bit#(indexW),Bit#(offsetW)) decode(Bit#(addrW) tag) decode;
} NBCacheConf#(numeric type tagW, numeric type indexW, numeric type offsetW, `TL_ARGS_DECL);

typedef enum {
  Idle, Lookup, ProbeLookup
} NBCacheState deriving(Bits, Eq, FShow);

module mkNBCacheCore#(
    NBCacheConf#(tagW,indexW,offsetW,`TL_ARGS) conf
  ) (NBCacheCore#(mshr,way,Bit#(tagW),Bit#(indexW),Bit#(offsetW),`TL_ARGS));

  Vector#(way, Bram#(Bit#(indexW), TLPerm)) permRam <- replicateM(mkBramInit(N));
  Vector#(way, Bram#(Bit#(indexW), Bit#(tagW))) tagRam <- replicateM(mkBram());
  Bram#(Bit#(indexW), PLRU#(way)) lruRam <- mkBram;

  Bit#(sizeW) logSize = fromInteger(valueOf(offsetW) + valueOf(TLog#(dataW)));

  Ehr#(2, NBCacheState) state <- mkEhr(Idle);

  Fifo#(2, Bit#(addrW)) evictQ <- mkFifo;

  let bram <- mkBramBE();
  Vector#(2, BramBE#(Bit#(TAdd#(TLog#(way), TAdd#(indexW, offsetW))), dataW)) vbram
    <- mkVectorBramBE(bram);

  Wire#(Bool) readBusy <- mkDWire(False);
  Wire#(Bool) writeBusy <- mkDWire(False);

  let readArbiter = interface ArbiterClient_IFC;
    method request = readBusy._write(True);
    method lock = noAction;
    method grant = True;
  endinterface;

  let writeArbiter = interface ArbiterClient_IFC;
    method request = writeBusy._write(True);
    method lock = noAction;
    method grant = True;
  endinterface;

  let vbram0 <- mkBramFromBramBE(vbram[0]);
  MshrFile#(mshr,TAdd#(TLog#(way), TAdd#(offsetW, indexW)), `TL_ARGS) mshr <-
    mkMshrFile(logSize, readArbiter, writeArbiter, vbram0);
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
  Reg#(Byte#(dataW)) data <- mkReg(?);
  Reg#(Bit#(dataW)) mask <- mkReg(?);
  Reg#(Bool) read <- mkReg(?);

  Reg#(Bit#(addrW)) probeAddr <- mkReg(?);
  Reg#(TLPerm) probePerm <- mkReg(?);

  // We can't run "lookup" or "lookupProbe" if one mshr can be free
  // to ensure forward progress (otherwise free can be blocked by retry requests)
  Wire#(Bool) didFree <- mkDWire(False);
  Wire#(Bool) canFree <- mkWire;

  Bool allowLookup = !canFree || didFree;

  rule canFreeRl;
    canFree <= mshr.canFree;
  endrule

  rule lookupProbe if (state[1] == Idle && allowLookup);
    match {.addr, .perm} <- mshr.probeStart();
    match {.tag, .idx, .off} = conf.decode(addr);

    probeAddr <= addr;
    probePerm <= perm;

    state[1] <= ProbeLookup;

    for (Integer i=0; i < valueOf(way); i = i + 1) begin
      permRam[i].read(idx);
      tagRam[i].read(idx);
    end
  endrule

  rule matchProbe if (state[0] == ProbeLookup);
    match {.t, .idx, .off} = conf.decode(probeAddr);
    Bit#(tagW) tag = ?;
    Token#(way) way = ?;
    TLPerm perm = N;

    state[0] <= Idle;

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
        evictQ.enq(probeAddr);
      end
      {T, B} : begin
        mshr.probeBlock(TtoB, {way,idx,0});
        permRam[way].write(idx, B);
      end
      {T, N} : begin
        mshr.probeBlock(TtoN, {way,idx,0});
        permRam[way].write(idx, N);
        evictQ.enq(probeAddr);
      end
    endcase
  endrule

  rule finishProbe;
    mshr.probeFinish();
  endrule

  method Action lookup(Bit#(indexW) idx, Bit#(offsetW) off, Bool r, Byte#(dataW) d, Bit#(dataW) m)
  if (state[1] == Idle && allowLookup && !mshr.canProbe);
    action
      read <= r;
      data <= d;
      mask <= m;
      index <= idx;
      offset <= off;
      state[1] <= Lookup;

      lruRam.read(idx);
      for (Integer i=0; i < valueof(way); i = i + 1) begin
        permRam[i].read(idx);
        tagRam[i].read(idx);
      end
    endaction
  endmethod

  method Action abort if (state[0] == Lookup);
    action
      lruRam.deq;
      for (Integer i=0; i < valueof(way); i = i + 1) begin
        permRam[i].deq;
        tagRam[i].deq;
      end

      state[0] <= Idle;
    endaction
  endmethod

  // TODO: improve the arbiter: we don't want to block if the request doesn't need the bram
  method ActionValue#(NBCacheAck#(mshr)) matching(Bit#(tagW) t)
    if (state[0] == Lookup && !(read && readBusy) && !(!read && writeBusy));

    PLRU#(way) lru = lruRam.response;
    Token#(way) way = PLRU::choose(lru);
    lruRam.deq;

    for (Integer i=0; i < valueof(way); i = i + 1) begin
      if (tagRam[i].response == t && permRam[i].response > N) begin
        way = fromInteger(i);
      end

      permRam[i].deq;
      tagRam[i].deq;
    end

    state[0] <= Idle;

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
    if (mshr.search(tr.next_addr,{way,index,0}) matches tagged Valid .m) begin
      return BlockedBy(m);
    end else if ((read && perm < B) || (!read && perm < T)) begin
      let tok_opt <- mshr.allocate(tr,{way,index,0});

      if (tok_opt matches tagged Valid .token) begin
        if (t != tag) evictQ.enq(conf.encode(tag,index,offset));
        lruRam.write(index, PLRU::next(lru,way));
        permRam[way].write(index,N);
        tagRam[way].write(index,t);
        return BlockedBy(token);
      end else
        return Blocked;
    end else begin
      lruRam.write(index, PLRU::next(lru,way));
      if (read) dataRam.read({way,index,offset});
      else dataRam.write({way,index,offset},data,mask);
      return Success;
    end
  endmethod

  method ActionValue#(Byte#(dataW)) response;
    dataRam.deq;
    return dataRam.response;
  endmethod

  method ActionValue#(Token#(mshr)) free if (state[0] == Idle);
    match {.m, .idx, .perm} <- mshr.free;
    match {.w,.i} = decodeIndex(idx);
    permRam[w].write(i,perm);
    didFree <= True;
    return m;
  endmethod

  interface evict = toFifoO(evictQ);

  interface master = mshr.master;

  method setSources = mshr.setSources;
endmodule
