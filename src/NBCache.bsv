import BlockRam :: *;
import TLServer :: *;
import TLTypes :: *;
import Vector :: *;
import Utils :: *;
import MSHR :: *;
import Fifo :: *;
import Ehr :: *;

export NBCacheCore(..);
export NBCacheConf(..);
export mkNBCacheCore;

`include "TL.defines"

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
      $display("allocate mshr: %d", m);
      permRam[way].write(index,N);
      tagRam[way].write(index,t);
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
