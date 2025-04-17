import BlockRam :: *;
import TLServer :: *;
import TLTypes :: *;
import Vector :: *;
import Utils :: *;
import Fifo :: *;
import Ehr :: *;

`include "TL.defines"



typedef union tagged {
  // Aligned Store
  struct {
    Byte#(dataW) data;
    Bit#(dataW) mask;
  } Store;

  // Load
  void Load;

  // LR/SC sequence
  struct {
    Byte#(dataW) data;
    Bit#(dataW) mask;
  } StoreConditional;

  void LoadReserve;

  // Stop the transaction, as example due to a MMU mis or fault between stage 1 and 2
  void Stop;
} CacheOp#(numeric type dataW) deriving(Bits, FShow, Eq);

function Bool needPermT(CacheOp#(dataW) op);
  return case (op) matches
    tagged StoreConditional .* : True;
    tagged Store .* : True;
    LoadReserve : True;
    default : False;
  endcase;
endfunction

function Bool isStoreConditional(CacheOp#(dataW) op);
  if (op matches tagged StoreConditional .*) return True;
  else return False;
endfunction

interface BCacheCore#(type tagT, type indexT, type offsetT, `TL_ARGS_DECL);
  method Action start(indexT index, offsetT offset);
  method Action matching(tagT tag, CacheOp#(dataW) op);
  method ActionValue#(Byte#(dataW)) response;
  method ActionValue#(Bool) success;

  method Action setSource(Bit#(sourceW) source);
endinterface

typedef struct {
  TLPerm perm;
  Bit#(tagW) tag;
  CacheOp#(dataW) op;
} BCacheInfo#(numeric type tagW, numeric type dataW)
deriving(FShow, Eq, Bits);

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
  // Acquire+Release a cache line
  Acquire,
  // Release a cache line (ex: Invalidation)
  Release,
  // Probe
  ProbeMatching,
  // Wait for the probe to acknoledge
  ProbeWait
} CacheState deriving(FShow, Eq, Bits);

// Invariant: the offset must correspond to the position of a beat in a cache block,
// this configuration can be used to implement banked ram, like even/odd indexes...
typedef struct {
  function Bit#(addrW) encode(Bit#(tagW) tag, Bit#(indexW) index, Bit#(offsetW) offset) encode;
  function Tuple3#(Bit#(tagW),Bit#(indexW),Bit#(offsetW)) decode(Bit#(addrW) tag) decode;
} BCacheConf#(numeric type tagW, numeric type indexW, numeric type offsetW, `TL_ARGS_DECL);


module mkBCacheCore
  #(BCacheConf#(tagW,indexW,offsetW,`TL_ARGS) conf, TLSlave#(`TL_ARGS) slave)
  (BCacheCore#(Bit#(tagW), Bit#(indexW), Bit#(offsetW), `TL_ARGS));

  Bram#(Bit#(indexW), TLPerm) permRam <- mkBramInit(N);
  Bram#(Bit#(indexW), Bit#(tagW)) tagRam <- mkBram();
  Bram#(Bit#(indexW), Bool) reservedRam <- mkBram();

  Bit#(sizeW) logSize = fromInteger(valueOf(offsetW) + valueOf(TLog#(dataW)));

  let bram <- mkBramBE();
  Vector#(2, BramBE#(Bit#(TAdd#(indexW, offsetW)), dataW)) vbram
    <- mkVectorBramBE(bram);

  let vbram0 <- mkBramFromBramBE(vbram[0]);
  AcquireFSM#(Bit#(TAdd#(offsetW, indexW)), `TL_ARGS) acquireM <-
    mkAcquireFSM(logSize, vbram0, slave);
  ReleaseFSM#(Bit#(TAdd#(offsetW, indexW)), `TL_ARGS) releaseM <-
    mkReleaseFSM(logSize, vbram0, slave);
  let dataRam = vbram[1];

  Fifo#(2, Bool) successQ <- mkFifo;

  Reg#(Bit#(indexW)) index <- mkReg(0);
  Reg#(Bit#(offsetW)) offset <- mkReg(0);
  Reg#(BCacheInfo#(tagW, dataW)) info <- mkReg(?);
  Reg#(BCacheProbeInfo#(tagW, indexW, offsetW)) probe <- mkReg(?);
  Ehr#(2, CacheState) state <- mkEhr(Idle);
  Reg#(CacheState) nextState <- mkReg(?);

  // Length of a cache line

  Reg#(Bit#(32)) numHit <- mkReg(0);
  Reg#(Bit#(32)) numMis <- mkReg(0);

  Reg#(Bit#(sourceW)) source <- mkReg(?);

  function Action doMiss(Bit#(tagW) tag, CacheOp#(dataW) op, TLPerm perm);
    action
      tagRam.write(index, tag);
      let tmp = info;
      tmp.perm = perm;
      tmp.tag = tag;
      tmp.op = op;
      info <= tmp;
    endaction
  endfunction

  rule releaseBlockAck if (state[0] == Release);
    releaseM.releaseAck();
    acquireM.acquireBlock(NtoT, {index, 0}, conf.encode(info.tag, index, 0));
    state[0] <= Acquire;
  endrule

  rule acquireBlockAck if (state[0] == Acquire);
    reservedRam.write(index, info.op == LoadReserve);
    let perm <- acquireM.acquireAck();
    permRam.write(index, perm);

    doAssert(perm >= info.perm, "Receive smaller permission than needed");

    state[0] <= Idle;

    case (info.op) matches
      Load : dataRam.read({index, offset});
      tagged Store .op : dataRam.write({index,offset}, op.data, op.mask);
      tagged LoadReserve : dataRam.read({index,offset});
      default: noAction;
    endcase
  endrule

  rule receiveProbe if (state[1] == Idle || state[1] == Acquire);
    match {.addr, .perm} <- releaseM.probeStart();

    match {.tag, .idx, .off} = conf.decode(addr);

    probe <= BCacheProbeInfo{
      offset: off,
      index: idx,
      perm: perm,
      tag: tag
    };

    permRam.read(idx);
    tagRam.read(idx);

    state[1] <= ProbeMatching;
    nextState <= state[1];
  endrule

  rule matchProbe if (state[0] == ProbeMatching);
    Bit#(tagW) tag = tagRam.response;
    TLPerm perm = tagRam.response == probe.tag ? permRam.response : N;

    permRam.deq();
    tagRam.deq();

    case (tuple2(perm, probe.perm)) matches
      {N, .*} : releaseM.probePerms(NtoN);
      {B, T} : releaseM.probePerms(BtoB);
      {B, B} : releaseM.probePerms(BtoB);
      {T, T} : releaseM.probePerms(TtoT);
      {B, N} : begin
        releaseM.probePerms(BtoN);
        permRam.write(probe.index, N);
        reservedRam.write(probe.index, False);
      end
      {T, B} : begin
        reservedRam.write(probe.index, False);
        releaseM.probeBlock(TtoB, {probe.index,0});
        permRam.write(probe.index, B);
      end
      {T, N} : begin
        reservedRam.write(probe.index, False);
        releaseM.probeBlock(TtoN, {probe.index,0});
        permRam.write(probe.index, N);
      end
    endcase
    state[0] <= ProbeWait;
  endrule

  rule finishProbe if (state[0] == ProbeWait);
    releaseM.probeFinish();
    state[0] <= nextState;
  endrule

  method Action start(Bit#(indexW) idx, Bit#(offsetW) off)
    if (state[1] == Idle);
    action
      index <= idx;
      offset <= off;
      state[1] <= Matching;
      reservedRam.read(idx);
      permRam.read(idx);
      tagRam.read(idx);
    endaction
  endmethod

  method Action matching(Bit#(tagW) t, CacheOp#(dataW) op)
    if (state[0] == Matching && dataRam.canRead);
    action
      Bit#(tagW) tag = tagRam.response;
      Bool reserved = reservedRam.response;
      TLPerm perm = tagRam.response == t ? permRam.response : N;

      Bool hit = perm == T || (perm == B && !needPermT(op));

      Bool stop = op == Stop || (!hit && isStoreConditional(op));

      reservedRam.deq();
      permRam.deq();
      tagRam.deq();

      if (hit) numHit <= numHit + 1;
      else numMis <= numMis + 1;

      if (isStoreConditional(op))
        successQ.enq(hit && reserved);

      if (stop) noAction;
      else if (hit) begin
        // Cache hit
        state[0] <= Idle;

        case (op) matches
          Load : dataRam.read({index, offset});
          LoadReserve : dataRam.read({index, offset});
          tagged Store .param : dataRam.write({index, offset}, param.data, param.mask);
          tagged StoreConditional .param : if (reserved)
            dataRam.write({index,offset}, param.data, param.mask);
          default : noAction;
        endcase

        reservedRam.write(index, op == LoadReserve);
      end else if (permRam.response == T) begin
        releaseM.releaseBlock(TtoN, {index, 0}, conf.encode(tag,index,0));
        permRam.write(index, N);
        state[0] <= Release;
        doMiss(t, op, T);
      end else begin
        doMiss(t, op, needPermT(op) ? T : B);
        state[0] <= Acquire;
        acquireM.acquireBlock(
          needPermT(op) ? (perm == N ? NtoT : BtoT) : NtoB,
          {index,0}, conf.encode(t, index, 0)
        );
      end
    endaction
  endmethod

  method ActionValue#(Byte#(dataW)) response;
    dataRam.deq();
    return dataRam.response();
  endmethod

  method ActionValue#(Bool) success;
    successQ.deq;
    return successQ.first;
  endmethod

  method Action setSource(Bit#(sourceW) src);
    action
      source <= src;
      acquireM.setSource(src);
      releaseM.setSource(src);
    endaction
  endmethod
endmodule
