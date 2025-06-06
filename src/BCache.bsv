import BlockRam :: *;
import TLMaster :: *;
import Arbiter :: *;
import TLTypes :: *;
import Vector :: *;
import TLUtils :: *;
import Fifo :: *;
import PLRU :: *;
import Ehr :: *;

export CacheOp(..);
export BCacheCore(..);
export BCacheConf(..);
export mkBCacheCore;

`include "TL.defines"

typedef union tagged {
  // Aligned Store
  struct {
    Bit#(dataW) data;
    Bit#(TDiv#(dataW,8)) mask;
  } Store;

  // Aligned Load
  void Load;

  // LR/SC sequence
  void LoadReserve;
  struct {
    Bit#(dataW) data;
    Bit#(TDiv#(dataW,8)) mask;
  } StoreConditional;

  // Atomic operations
  atomicOp Atomic;
} CacheOp#(type atomicOp, numeric type dataW) deriving(Bits, FShow);

// Return if an operation need the T (Read+Write) permission to be performed
// LoadReserve need this permission, overwise the next StoreConditional will
// always fail
function Bool needPermT(CacheOp#(atomicOp, dataW) op);
  return case (op) matches
    tagged StoreConditional .* : True;
    tagged Atomic .* : True;
    tagged Store .* : True;
    LoadReserve : True;
    default : False;
  endcase;
endfunction

function Bool isStoreConditional(CacheOp#(atomicOp, dataW) op);
  if (op matches tagged StoreConditional .*) return True;
  else return False;
endfunction

function Bool isLoadReserve(CacheOp#(atomicOp, dataW) op);
  if (op matches LoadReserve) return True;
  else return False;
endfunction

function Bool isLoad(CacheOp#(atomicOp, dataW) op);
  if (op matches Load) return True;
  else return False;
endfunction

interface BCacheCore
  #(type atomicOp, numeric type numWay, type tagT, type indexT, type offsetT, `TL_ARGS_DECL);
  method Action lookup(indexT index, offsetT offset);
  method Action matching(tagT tag, CacheOp#(atomicOp, dataW) op);
  method Action abort;
  method ActionValue#(Bit#(dataW)) loadResponse;
  method ActionValue#(Bit#(dataW)) atomicResponse;
  method ActionValue#(Bool) success;

  /*** Inform the host CPU that we evict a cache block ***/
  interface FifoO#(Bit#(addrW)) evict;

  method Action setSource(Bit#(sourceW) source);
endinterface

typedef struct {
  TLPerm perm;
  Bit#(tagW) tag;
  Token#(numWay) way;
  CacheOp#(atomicOp, dataW) op;
} BCacheInfo#(type atomicOp, numeric type numWay, numeric type tagW, numeric type dataW)
deriving(FShow, Bits);

typedef struct {
  Bit#(tagW) tag;
  Bit#(indexW) index;
  Bit#(offsetW) offset;
  TLPerm perm;
} BCacheProbeInfo#(numeric type tagW, numeric type indexW, numeric type offsetW)
deriving(FShow, Eq, Bits);

typedef enum {
  // Wait for a request
  Idle,
  // Wait for matching
  Matching,
  // Acquire a cache line
  Acquire,
  // Release (then acquire) a cache line
  Release,
  // Invalidations requests from the cache controller
  ProbeMatching,
  // Wait for the probe to acknoledge
  ProbeWait
} CacheState deriving(FShow, Eq, Bits);

// Invariant: the offset must correspond to the position of a beat in a cache block,
// this configuration can be used to implement banked ram, like even/odd indexes...
// It also contains the necessary function to execute an atomic operation
typedef struct {
  function Bit#(addrW) encode(Bit#(tagW) tag, Bit#(indexW) index, Bit#(offsetW) offset) encode;
  function Tuple3#(Bit#(tagW),Bit#(indexW),Bit#(offsetW)) decode(Bit#(addrW) tag) decode;
  function Bit#(dataW) atomic(atomicOp atomic, Bit#(dataW) value) atomic;
} BCacheConf
#(type atomicOp, numeric type tagW, numeric type indexW, numeric type offsetW, `TL_ARGS_DECL);

module mkBCacheCore
  #(BCacheConf#(atomicOp, tagW,indexW,offsetW,`TL_ARGS) conf, TLSlave#(`TL_ARGS) slave)
  (BCacheCore#(atomicOp, numWay, Bit#(tagW), Bit#(indexW), Bit#(offsetW), `TL_ARGS))
  provisos(Bits#(atomicOp, atomicOpW));

  Reg#(Bool) started <- mkReg(False);

  Vector#(numWay, Bram#(Bit#(indexW), TLPerm)) permRam <- replicateM(mkBramInit(N));
  Vector#(numWay, Bram#(Bit#(indexW), Bit#(tagW))) tagRam <- replicateM(mkBram());
  Bram#(Bit#(indexW), PLRU#(numWay)) lruRam <- mkBram();

  Bit#(sizeW) logSize = fromInteger(valueOf(offsetW) + log2(valueOf(dataW)/8));

  Ehr#(2, Bit#(8)) reservedTimer <- mkEhr(0);
  Reg#(Bool) reserved <- mkReg(False);

  Action reserve = action
    reservedTimer[1] <= 32;
    reserved <= True;
  endaction;

  Action unreserve = action
    reservedTimer[1] <= 0;
    reserved <= False;
  endaction;

  rule decrement_reserved if (reservedTimer[0] > 0);
    reservedTimer[0] <= reservedTimer[0] - 1;
  endrule

  let bram <- mkBramBE();
  Vector#(2, BramBE#(Bit#(TAdd#(TLog#(numWay), TAdd#(indexW, offsetW))), dataW)) vbram
    <- mkVectorBramBE(bram);

  // As this cache is blocking it's not necessary to use an arbiter here
  ArbiterClient_IFC arbiter = interface ArbiterClient_IFC;
    method request = noAction;
    method lock = noAction;
    method grant = True;
  endinterface;


  let vbram0 <- mkBramFromBramBE(vbram[0]);
  AcquireMaster#(Bit#(TAdd#(TLog#(numWay), TAdd#(offsetW, indexW))), `TL_ARGS) acquireM <-
    mkAcquireMaster(logSize, slave, arbiter, vbram0);
  ReleaseMaster#(Bit#(TAdd#(TLog#(numWay), TAdd#(offsetW, indexW))), `TL_ARGS) releaseM <-
    mkReleaseMaster(logSize, slave, arbiter, vbram0);
  let dataRam = vbram[1];

  Fifo#(2, Bool) successQ <- mkFifo;

  Fifo#(2, Bit#(addrW)) evictQ <- mkFifo;

  Reg#(Bit#(indexW)) index <- mkReg(0);
  Reg#(Bit#(offsetW)) offset <- mkReg(0);
  Reg#(BCacheInfo#(atomicOp, numWay, tagW, dataW)) info <- mkReg(?);
  Reg#(BCacheProbeInfo#(tagW, indexW, offsetW)) probe <- mkReg(?);
  Ehr#(2, CacheState) state <- mkEhr(Idle);
  Reg#(CacheState) nextState <- mkReg(?);

  Reg#(Bit#(32)) numHit <- mkReg(0);
  Reg#(Bit#(32)) numMis <- mkReg(0);

  Reg#(Bit#(sourceW)) source <- mkReg(?);

  // Saved informations at matching stage to perform atomic operations
  Reg#(CacheOp#(atomicOp, dataW)) pendingOp <- mkReg(?);
  Reg#(Bit#(TAdd#(TLog#(numWay), TAdd#(offsetW, indexW)))) pendingPos <- mkReg(?);

  function Action doMiss(Token#(numWay) way, Bit#(tagW) tag, CacheOp#(atomicOp, dataW) op, TLPerm perm);
    action
      let tmp = info;
      tmp.perm = perm;
      tmp.way = way;
      tmp.tag = tag;
      tmp.op = op;
      info <= tmp;
    endaction
  endfunction

  rule releaseBlockAck if (state[0] == Release && started);
    acquireM.acquireBlock(NtoT, {info.way, index, 0}, conf.encode(info.tag, index, 0));
    releaseM.releaseAck();
    state[0] <= Acquire;
  endrule

  rule acquireBlockAck if (state[0] == Acquire && started);
    let perm <- acquireM.acquireAck();

    doAssert(perm >= info.perm, "Receive smaller permission than needed");

    perm = needPermT(info.op) && !isLoadReserve(info.op) ? D : perm;
    tagRam[info.way].write(index, info.tag);
    permRam[info.way].write(index, perm);

    state[0] <= Idle;

    if (isLoadReserve(info.op)) reserve();

    case (info.op) matches
      Load : dataRam.read({info.way, index, offset});
      tagged Store .op : dataRam.write({info.way,index,offset}, op.data, op.mask);
      tagged LoadReserve : dataRam.read({info.way,index,offset});
      default: noAction;
    endcase
  endrule

  Bool canProbe =
    (state[1] == Idle || state[1] == Acquire) && reservedTimer[1] == 0 && releaseM.canProbe;

  rule lookupProbe if (canProbe && started);
    match {.addr, .perm} <- releaseM.probeStart();

    match {.tag, .idx, .off} = conf.decode(addr);

    probe <= BCacheProbeInfo{
      offset: off,
      index: idx,
      perm: perm,
      tag: tag
    };

    for (Integer i=0; i < valueOf(numWay); i = i + 1) begin
      permRam[i].read(idx);
      tagRam[i].read(idx);
    end

    state[1] <= ProbeMatching;
    nextState <= state[1];
  endrule

  rule matchProbe if (state[0] == ProbeMatching && started);
    Bit#(tagW) tag = ?;
    Token#(numWay) way = ?;
    TLPerm perm = N;

    for (Integer i=0; i < valueOf(numWay); i = i + 1) begin
      if (tagRam[i].response == probe.tag && permRam[i].response > N) begin
        perm = permRam[i].response;
        way = fromInteger(i);
      end

      permRam[i].deq;
      tagRam[i].deq;
    end

    // Same action for a Dirty and Thrunk cache block
    perm = perm == D ? T : perm;

    case (tuple2(perm, probe.perm)) matches
      {N, .*} : releaseM.probePerms(NtoN);
      {B, T} : releaseM.probePerms(BtoB);
      {B, B} : releaseM.probePerms(BtoB);
      {T, T} : releaseM.probePerms(TtoT);
      {B, N} : begin
        releaseM.probePerms(BtoN);
        permRam[way].write(probe.index, N);
        evictQ.enq(conf.encode(tag, probe.index, 0));
        unreserve();
      end
      {T, B} : begin
        releaseM.probeBlock(TtoB, {way,probe.index,0});
        permRam[way].write(probe.index, B);
        unreserve();
      end
      {T, N} : begin
        releaseM.probeBlock(TtoN, {way,probe.index,0});
        evictQ.enq(conf.encode(tag, probe.index, 0));
        permRam[way].write(probe.index, N);
        unreserve();
      end
    endcase
    state[0] <= ProbeWait;
  endrule

  rule finishProbe if (state[0] == ProbeWait && started);
    releaseM.probeFinish();
    state[0] <= nextState;
  endrule

  method Action lookup(Bit#(indexW) idx, Bit#(offsetW) off)
    if (state[1] == Idle && !canProbe && started);
    action
      index <= idx;
      offset <= off;
      lruRam.read(idx);
      state[1] <= Matching;
      for (Integer i=0; i < valueOf(numWay); i = i + 1) begin
        permRam[i].read(idx);
        tagRam[i].read(idx);
      end
    endaction
  endmethod

  method Action abort if (state[0] == Matching && started);
    lruRam.deq;
    state[0] <= Idle;
    for (Integer i=0; i < valueOf(numWay); i = i + 1) begin
      permRam[i].deq;
      tagRam[i].deq;
    end
  endmethod

  method Action matching(Bit#(tagW) t, CacheOp#(atomicOp, dataW) op)
    if (state[0] == Matching && dataRam.canRead && started);
    action
      doAssert(2**log2(valueOf(numWay)) == valueOf(numWay), "\"numWay\" must be a power of 2");

      PLRU#(numWay) lru = lruRam.response;
      Token#(numWay) way = PLRU::choose(lru);
      Bit#(tagW) tag = tagRam[way].response;
      TLPerm perm = N;

      lruRam.deq;

      for (Integer i=0; i < valueOf(numWay); i = i + 1) begin
        if (tagRam[i].response == t && permRam[i].response > N) begin
          perm = permRam[i].response;
          way = fromInteger(i);
          tag = t;
        end

        permRam[i].deq();
        tagRam[i].deq();
      end

      Bool hit = perm >= T || (perm == B && !needPermT(op));
      Bool stop = !hit && isStoreConditional(op);

      if (!stop) lruRam.write(index, PLRU::next(lru, way));

      if (hit) numHit <= numHit + 1;
      else numMis <= numMis + 1;

      //$display("source: %d hit: %d mis: %d", source, numHit, numMis);

      if (isStoreConditional(op))
        successQ.enq(hit && reserved);

      if (hit && isLoadReserve(op)) reserve();
      else unreserve();

      pendingOp <= op;
      pendingPos <= {way, index, offset};

      if (stop) state[0] <= Idle;
      else if (hit) begin
        // Cache hit
        state[0] <= Idle;

        case (op) matches
          Load : dataRam.read({way, index, offset});
          LoadReserve : dataRam.read({way, index, offset});
          tagged Store .param : dataRam.write({way, index, offset}, param.data, param.mask);
          tagged StoreConditional .param : if (reserved)
            dataRam.write({way, index,offset}, param.data, param.mask);
          default : noAction;
        endcase

        // Set the cache block as dirty
        if (needPermT(op) && !isLoadReserve(op)) permRam[way].write(index, D);

      end else if (t != tag && permRam[way].response != N) begin

        let address = conf.encode(tag,index,0);
        case (permRam[way].response) matches
          D : releaseM.releaseBlock(TtoN, {way, index, 0}, address);
          T : releaseM.releasePerms(TtoN, address);
          B : releaseM.releasePerms(BtoN, address);
        endcase

        evictQ.enq(address);

        case (permRam[way].response) matches
          D: state[0] <= Release;
          default: state[0] <= Release;
        endcase

        doMiss(way, t, op, needPermT(op) ? T : B);
        permRam[way].write(index, N);
      end else begin
        doMiss(way, t, op, needPermT(op) ? T : B);

        state[0] <= Acquire;
        acquireM.acquireBlock(
          needPermT(op) ? (perm == N ? NtoT : BtoT) : NtoB,
          {way, index,0}, conf.encode(t, index, 0)
        );
      end
    endaction
  endmethod

  method ActionValue#(Bit#(dataW)) loadResponse
    if (started && (isLoad(pendingOp) || isLoadReserve(pendingOp)));
    dataRam.deq();

    return dataRam.response;
  endmethod

  method ActionValue#(Bit#(dataW)) atomicResponse
    if (started &&& pendingOp matches tagged Atomic .atomic);
    dataRam.write(pendingPos, conf.atomic(atomic, dataRam.response), ~0);
    dataRam.deq();

    return dataRam.response;
  endmethod

  method ActionValue#(Bool) success;
    successQ.deq;
    return successQ.first;
  endmethod

  method Action setSource(Bit#(sourceW) src) if (!started);
    action
      source <= src;
      started <= True;
      acquireM.setSource(src);
      releaseM.setSource(src);
    endaction
  endmethod

  interface evict = toFifoO(evictQ);
endmodule
