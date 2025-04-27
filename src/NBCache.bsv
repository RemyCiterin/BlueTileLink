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

  // Stop the transaction, as example due to a MMU mis or fault between stage 1 and 2
  void Stop;
} CacheOp#(numeric type dataW) deriving(Bits, FShow, Eq);

// Return if an operation need the T (Read+Write) permission to be performed
// LoadReserve need this permission, overwise the next StoreConditional will
// always fail
function Bool needPermT(CacheOp#(dataW) op);
  return case (op) matches
    tagged Store .* : True;
    default : False;
  endcase;
endfunction

interface NBCacheCore
  #(numeric type mshr, type idT, type wayT, type tagT, type indexT, type offsetT, `TL_ARGS_DECL);
  method Action start(idT id, indexT index, offsetT offset);
  method Action matching(tagT tag, CacheOp#(dataW) op);
    method ActionValue#(Tuple2#(idT, Byte#(dataW))) response;

  // Set sources for acquire and release requests
  method Action setSource(Vector#(mshr, Bit#(sourceW)) acqSources, Bit#(sourceW) relSource);
endinterface

typedef struct {
  TLPerm perm;
  Bit#(wayW) way;
  Bit#(tagW) tag;
  CacheOp#(dataW) op;
} BCacheInfo#(numeric type wayW, numeric type tagW, numeric type dataW)
deriving(FShow, Eq, Bits);

// Global information about a cache miss
typedef struct {
  // True if the acquire is not finish
  Bool valid;

  // Requested permission
  TLPerm perm;

  // Way of the request
  Bit#(wayW) way;

  // Tag of the request
  Bit#(tagW) tag;

  // Index of the request
  Bit#(indexW) index;
} MissInfo#(numeric type wayW, numeric type tagW);

// Local informations about a cache miss (specific to the miss request)
typedef struct {
  Bit#(offsetW) offset;
  CacheOp#(dataW) op;
} ReqInfo#(numeric type offsetW, numeric type dataW);

typedef struct {
  Bit#(tagW) tag;
  Bit#(indexW) index;
  Bit#(offsetW) offset;
  Maybe#(Grow) state;
  TLPerm perm;
} ProbeInfo#(numeric type tagW, numeric type indexW, numeric type offsetW)
deriving(FShow, Eq, Bits);

// Invariant: the offset must correspond to the position of a beat in a cache block,
// this configuration can be used to implement banked ram, like even/odd indexes...
typedef struct {
  function Bit#(addrW) encode(Bit#(tagW) tag, Bit#(indexW) index, Bit#(offsetW) offset) encode;
  function Tuple3#(Bit#(tagW),Bit#(indexW),Bit#(offsetW)) decode(Bit#(addrW) tag) decode;
} BCacheConf#(numeric type tagW, numeric type indexW, numeric type offsetW, `TL_ARGS_DECL);

typedef union tagged {
  // The cache block is ready to be used
  TLPerm Idle;

  // Their is an acquire request on the cache block
  Grow Acquire;

  // The cache block is being reduced by a probe
  Reduce Probe;

  // The cache block is being reduced by a release
  Reduce Release;
} BlockState deriving(Bits, FShow, Eq);

module mkNBCacheCore
  #(BCacheConf#(tagW,indexW,offsetW,`TL_ARGS) conf, TLSlave#(`TL_ARGS) slave)
  (NBCacheCore#(mshrN, idT, Bit#(wayW), Bit#(tagW), Bit#(indexW), Bit#(offsetW), `TL_ARGS))
  provisos(Bits#(idT, idW));

  Vector#(TExp#(wayW), Bram#(Bit#(indexW), BlockState)) stateRam <- replicateM(mkBramInit(Idle(N)));
  Vector#(TExp#(wayW), Bram#(Bit#(indexW), Bit#(tagW))) tagRam <- replicateM(mkBram());

  Bit#(sizeW) logSize = fromInteger(valueOf(offsetW) + valueOf(TLog#(dataW)));

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
  Vector#(2, BramBE#(Bit#(TAdd#(wayW, TAdd#(indexW, offsetW))), dataW)) vbram
    <- mkVectorBramBE(bram);

  let vbram0 <- mkBramFromBramBE(vbram[0]);
  AcquireFSM#(Bit#(TAdd#(wayW, TAdd#(offsetW, indexW))), `TL_ARGS) acquireM <-
    mkAcquireFSM(logSize, vbram0, slave);
    ReleaseFSM#(Bit#(TAdd#(wayW, TAdd#(offsetW, indexW))), `TL_ARGS) releaseM <-
    mkReleaseFSM(logSize, vbram0, slave);
  let dataRam = vbram[1];

  Reg#(Bit#(wayW)) randomWay <- mkReg(0);

  rule updateRandomWay;
    randomWay <= randomWay + 1;
  endrule

  Fifo#(2, Bool) successQ <- mkFifo;

  Reg#(Bit#(indexW)) index <- mkReg(0);
  Reg#(Bit#(offsetW)) offset <- mkReg(0);
  Reg#(BCacheInfo#(wayW, tagW, dataW)) info <- mkReg(?);
  Reg#(ProbeInfo#(tagW, indexW, offsetW)) probe <- mkReg(?);
  Ehr#(2, CacheState) state <- mkEhr(Idle);
  Reg#(CacheState) nextState <- mkReg(?);

  // Length of a cache line

  Reg#(Bit#(32)) numHit <- mkReg(0);
  Reg#(Bit#(32)) numMis <- mkReg(0);

  Reg#(Bit#(sourceW)) source <- mkReg(?);

  function Action doMiss(Bit#(wayW) way, Bit#(tagW) tag, CacheOp#(dataW) op, TLPerm perm);
    action
      let tmp = info;
      tmp.perm = perm;
      tmp.way = way;
      tmp.tag = tag;
      tmp.op = op;
      info <= tmp;
    endaction
  endfunction

  rule releaseBlockAck if (state[0] == Release);
    releaseM.releaseAck();
    acquireM.acquireBlock(NtoT, {info.way, index, 0}, conf.encode(info.tag, index, 0));
    state[0] <= Acquire;
  endrule

  rule acquireBlockAck if (state[0] == Acquire);
    let perm <- acquireM.acquireAck();
    permRam[info.way].write(index, perm);
    tagRam[info.way].write(index, info.tag);

    doAssert(perm >= info.perm, "Receive smaller permission than needed");

    state[0] <= Idle;

    if (info.op == LoadReserve) reserve();

    case (info.op) matches
      Load : dataRam.read({info.way, index, offset});
      tagged Store .op : dataRam.write({info.way,index,offset}, op.data, op.mask);
      tagged LoadReserve : dataRam.read({info.way,index,offset});
      default: noAction;
    endcase
  endrule

  method Action start(Bit#(indexW) idx, Bit#(offsetW) off)
    if (state[1] == Idle);
    action
      index <= idx;
      offset <= off;
      state[1] <= Matching;
      for (Integer i=0; i < valueOf(TExp#(wayW)); i = i + 1) begin
        permRam[i].read(idx);
        tagRam[i].read(idx);
      end
    endaction
  endmethod

  method Action matching(Bit#(tagW) t, CacheOp#(dataW) op)
    if (state[0] == Matching && dataRam.canRead);
    action
      Bit#(wayW) way = randomWay;
      Bit#(tagW) tag = tagRam[way].response;
      TLPerm perm = N;

      for (Integer i=0; i < valueOf(TExp#(wayW)); i = i + 1) begin
        if (tagRam[i].response == t && permRam[i].response > N) begin
          perm = permRam[i].response;
          way = fromInteger(i);
          tag = t;
        end

        permRam[i].deq();
        tagRam[i].deq();
      end

      Bool hit = perm == T || (perm == B && !needPermT(op));
      Bool stop = op == Stop || (!hit && isStoreConditional(op));

      if (hit) numHit <= numHit + 1;
      else numMis <= numMis + 1;

      if (isStoreConditional(op))
        successQ.enq(hit && reserved);

      if (hit && op == LoadReserve) reserve();
      else unreserve();

      if (stop) noAction;
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

      end else if (permRam[way].response == T) begin
        releaseM.releaseBlock(TtoN, {way, index, 0}, conf.encode(tag,index,0));
        permRam[way].write(index, N);
        doMiss(way, t, op, T);
        state[0] <= Release;
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
