import FIFOF :: *;
import SpecialFIFOs :: *;
import BypassReg :: *;
import BRAMCore :: *;
import Vector :: *;
import Array :: *;
import TLUtils :: *;
import RegFile :: *;

import Ehr :: *;


interface Bram#(type addrT, type dataT);
  method Action write(addrT addr, dataT data);
  method Action read(addrT addr);
  method dataT response;
  method Bool canRead;
  method Bool canDeq;
  method Action deq;
endinterface

module wrapBramRegFile#(RegFile#(addrT, dataT) rf) (Bram#(addrT,dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  FIFOF#(Maybe#(dataT)) rsp <- mkPipelineFIFOF;

  Reg#(dataT) dout <- mkReg(?);

  RWire#(dataT) currentWrData <- mkRWire;
  RWire#(addrT) currentWrAddr <- mkRWire;
  let wrAddr = fromMaybe(?, currentWrAddr.wget);
  let wrData = fromMaybe(?, currentWrData.wget);
  let wrValid = isJust(currentWrAddr.wget);

  RWire#(addrT) currentRdAddr <- mkRWire;
  let rdAddr = fromMaybe(?, currentRdAddr.wget);
  let rdValid = isJust(currentRdAddr.wget);

  (* no_implicit_conditions, fire_when_enabled *)
  rule block_ram_apply_write if (wrValid);
    rf.upd(wrAddr, wrData);
  endrule

  (* fire_when_enabled *)
  rule block_ram_apply_read if (rdValid && rsp.notFull());
    let data = (wrValid && wrAddr == rdAddr ? Valid(wrData) : Invalid);
    dout <= rf.sub(rdAddr);
    rsp.enq(data);
  endrule

  method Action write(addrT addr, dataT data);
    currentWrAddr.wset(addr);
    currentWrData.wset(data);
  endmethod

  method Action read(addrT addr) if (rsp.notFull());
    currentRdAddr.wset(addr);
  endmethod

  method Bool canRead = rsp.notFull;

  method dataT response if (rsp.notEmpty);
    case (rsp.first) matches
      tagged Valid .data : return data;
      tagged Invalid: return dout;
    endcase
  endmethod

  method canDeq = rsp.notEmpty;

  method deq = rsp.deq;
endmodule

module wrapBram
  #(BRAM_DUAL_PORT#(addrT,dataT) bram) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  FIFOF#(Maybe#(dataT)) rsp <- mkPipelineFIFOF;
  let wrPort = bram.a;
  let rdPort = bram.b;

  // currentData and currentAddr contain the arguments of the last write
  RWire#(dataT) currentWrData <- mkRWire;
  RWire#(addrT) currentWrAddr <- mkRWire;
  let wrAddr = fromMaybe(?, currentWrAddr.wget);
  let wrData = fromMaybe(?, currentWrData.wget);
  let wrValid = isJust(currentWrAddr.wget);

  RWire#(addrT) currentRdAddr <- mkRWire;
  let rdAddr = fromMaybe(?, currentRdAddr.wget);
  let rdValid = isJust(currentRdAddr.wget);

  (* no_implicit_conditions, fire_when_enabled *)
  rule block_ram_apply_write if (wrValid);
    wrPort.put(True, wrAddr, wrData);
  endrule

  (* fire_when_enabled *)
  rule block_ram_apply_read if (rdValid && rsp.notFull());
    let data = (wrValid && wrAddr == rdAddr ? Valid(wrData) : Invalid);
    rdPort.put(False, rdAddr, ?);
    rsp.enq(data);
  endrule

  method Action write(addrT addr, dataT data);
    currentWrAddr.wset(addr);
    currentWrData.wset(data);
  endmethod

  method Action read(addrT addr) if (rsp.notFull());
    currentRdAddr.wset(addr);
  endmethod

  method Bool canRead = rsp.notFull;

  method dataT response if (rsp.notEmpty);
    case (rsp.first) matches
      tagged Valid .data : return data;
      tagged Invalid: return rdPort.read;
    endcase
  endmethod

  method canDeq = rsp.notEmpty;

  method deq = rsp.deq;
endmodule

module mkSizedBram#(Integer size) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  BRAM_DUAL_PORT#(addrT, dataT) bram <- mkBRAMCore2(size, False);
  let ifc <- wrapBram(bram);
  return ifc;
endmodule

module mkSizedBramLoad#(Integer size, String file, Bool binary) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  BRAM_DUAL_PORT#(addrT, dataT) bram <- mkBRAMCore2Load(size, False, file, binary);
  let ifc <- wrapBram(bram);
  return ifc;
endmodule

// return an initialized block of ram
module mkSizedBramGen
  #(Integer size, function dataT gen(addrT addr)) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  Bram#(addrT, dataT) bram <- mkSizedBram(size);

  Reg#(Maybe#(Bit#(addrWidth))) startIndex <- mkReg(Valid(0));

  rule init_register_file if (startIndex matches tagged Valid .index);
    startIndex <= index == fromInteger(size - 1) ? Invalid : Valid (index + 1);
    bram.write(unpack(index), gen(unpack(index)));
  endrule

  method Action read(addrT addr) if (startIndex == Invalid);
    bram.read(addr);
  endmethod

  method Bool canRead = startIndex == Invalid && bram.canRead;

  method dataT response if (startIndex == Invalid);
    return bram.response();
  endmethod

  method Action deq() if (startIndex == Invalid);
    bram.deq();
  endmethod

  method canDeq = bram.canDeq && startIndex == Invalid;

  method Action write(addrT addr, dataT data) if (startIndex == Invalid);
    bram.write(addr, data);
  endmethod
endmodule

module mkSizedBramInit#(Integer size, dataT init) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  let ifc <- mkSizedBramGen(size, constFn(init));
  return ifc;
endmodule

module mkBram(Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  let ifc <- mkSizedBram(valueOf(TExp#(addrWidth)));
  return ifc;
endmodule

module mkBramGen#(function dataT gen(addrT addr)) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  let ifc <- mkSizedBramGen(valueOf(TExp#(addrWidth)), gen);
  return ifc;
endmodule

module mkBramInit#(dataT init) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  let ifc <- mkSizedBramInit(valueOf(TExp#(addrWidth)), init);
  return ifc;
endmodule

interface BramVec#(type addrT, numeric type n, type dataT);
  method Action write(addrT addr, Vector#(n, dataT) data, Bit#(n) mask);
  method Action read(addrT addr);
  method Vector#(n, dataT) response;
  method Bool canRead;
  method Bool canDeq;
  method Action deq;
endinterface

module wrapBramVecRegFile#(Vector#(n, RegFile#(addrT,dataT)) rf) (BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT), Bits#(dataT, dataW));

  FIFOF#(Tuple2#(Vector#(n, dataT), Bit#(n))) rsp <- mkPipelineFIFOF;

  Vector#(n, Reg#(dataT)) dout <- replicateM(mkReg(?));

  // currentData and currentAddr contain the arguments of the last write
  RWire#(addrT) currentWrAddr <- mkRWire;
  RWire#(Bit#(n)) currentWrMask <- mkRWire;
  RWire#(Vector#(n, dataT)) currentWrData <- mkRWire;
  let wrAddr = fromMaybe(?, currentWrAddr.wget);
  let wrData = fromMaybe(?, currentWrData.wget);
  let wrMask = fromMaybe(?, currentWrMask.wget);
  let wrValid = isJust(currentWrAddr.wget);

  RWire#(addrT) currentRdAddr <- mkRWire;
  let rdAddr = fromMaybe(?, currentRdAddr.wget);
  let rdValid = isJust(currentRdAddr.wget);

  (* no_implicit_conditions, fire_when_enabled *)
  rule block_ram_apply_write if (wrValid);
    for (Integer i=0; i < valueOf(n); i = i + 1) if (wrMask[i] == 1) begin
      rf[i].upd(wrAddr, wrData[i]);
    end
  endrule

  (* fire_when_enabled *)
  rule block_ram_apply_read if (rdValid && rsp.notFull());
    let data = tuple2(wrData, wrValid && wrAddr == rdAddr ? wrMask : 0);

    for (Integer i=0; i < valueOf(n); i = i + 1) begin
      dout[i] <= rf[i].sub(rdAddr);
    end

    rsp.enq(data);
  endrule

  method Action write(addrT addr, Vector#(n, dataT) data, Bit#(n) mask);
    currentWrAddr.wset(addr);
    currentWrData.wset(data);
    currentWrMask.wset(mask);
  endmethod

  method Action read(addrT addr) if (rsp.notFull());
    currentRdAddr.wset(addr);
  endmethod

  method Bool canRead = rsp.notFull;

  method Vector#(n, dataT) response if (rsp.notEmpty);
    match {.data, .mask} = rsp.first;
    Vector#(n, dataT) ret = data;

    for (Integer i=0; i < valueOf(n); i = i + 1) begin
      if (mask[i] == 0) ret[i] = dout[i];
    end

    return ret;
  endmethod

  method canDeq = rsp.notEmpty;

  method deq = rsp.deq;
endmodule

module mkSizedBramVec#(Integer size) (BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT), Bits#(dataT, dataW));
  Vector#(n, BRAM_DUAL_PORT#(addrT, dataT)) bram <-
    replicateM(mkBRAMCore2(size, False));

  FIFOF#(Tuple2#(Vector#(n, dataT), Bit#(n))) rsp <- mkPipelineFIFOF;

  // currentData and currentAddr contain the arguments of the last write
  RWire#(addrT) currentWrAddr <- mkRWire;
  RWire#(Bit#(n)) currentWrMask <- mkRWire;
  RWire#(Vector#(n, dataT)) currentWrData <- mkRWire;
  let wrAddr = fromMaybe(?, currentWrAddr.wget);
  let wrData = fromMaybe(?, currentWrData.wget);
  let wrMask = fromMaybe(?, currentWrMask.wget);
  let wrValid = isJust(currentWrAddr.wget);

  RWire#(addrT) currentRdAddr <- mkRWire;
  let rdAddr = fromMaybe(?, currentRdAddr.wget);
  let rdValid = isJust(currentRdAddr.wget);

  (* no_implicit_conditions, fire_when_enabled *)
  rule block_ram_apply_write if (wrValid);
    for (Integer i=0; i < valueOf(n); i = i + 1) if (wrMask[i] == 1) begin
      bram[i].a.put(True, wrAddr, wrData[i]);
    end
  endrule

  (* fire_when_enabled *)
  rule block_ram_apply_read if (rdValid && rsp.notFull());
    let data = tuple2(wrData, wrValid && wrAddr == rdAddr ? wrMask : 0);

    for (Integer i=0; i < valueOf(n); i = i + 1) begin
      bram[i].b.put(False, rdAddr, ?);
    end

    rsp.enq(data);
  endrule

  method Action write(addrT addr, Vector#(n, dataT) data, Bit#(n) mask);
    currentWrAddr.wset(addr);
    currentWrData.wset(data);
    currentWrMask.wset(mask);
  endmethod

  method Action read(addrT addr) if (rsp.notFull());
    currentRdAddr.wset(addr);
  endmethod

  method Bool canRead = rsp.notFull;

  method Vector#(n, dataT) response if (rsp.notEmpty);
    match {.data, .mask} = rsp.first;
    Vector#(n, dataT) ret = data;

    for (Integer i=0; i < valueOf(n); i = i + 1) begin
      if (mask[i] == 0) ret[i] = bram[i].b.read;
    end

    return ret;
  endmethod

  method canDeq = rsp.notEmpty;

  method deq = rsp.deq;
endmodule

// return an initialized block of ram
module mkSizedBramGenVec
  #(Integer size, function Vector#(n, dataT) gen(addrT addr)) (BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  BramVec#(addrT, n, dataT) bram <- mkSizedBramVec(size);

  Reg#(Maybe#(Bit#(addrWidth))) startIndex <- mkReg(Valid(0));

  rule init_register_file if (startIndex matches tagged Valid .index);
    startIndex <= index == fromInteger(size - 1) ? Invalid : Valid (index + 1);
    bram.write(unpack(index), gen(unpack(index)), -1);
  endrule

  method Action read(addrT addr) if (startIndex == Invalid);
    bram.read(addr);
  endmethod

  method canRead = startIndex == Invalid && bram.canRead;

  method Vector#(n, dataT) response if (startIndex == Invalid);
    return bram.response();
  endmethod

  method Action deq() if (startIndex == Invalid);
    bram.deq();
  endmethod

  method canDeq = bram.canDeq && startIndex == Invalid;

  method Action write(addrT addr, Vector#(n, dataT) data, Bit#(n) mask)
    if (startIndex == Invalid);
    bram.write(addr, data, mask);
  endmethod
endmodule

module mkSizedBramInitVec
  #(Integer size, Vector#(n, dataT) init) (BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  let ifc <- mkSizedBramGenVec(size, constFn(init));
  return ifc;
endmodule

module mkBramVec(BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT), Bits#(dataT, dataW));
  let ifc <- mkSizedBramVec(valueOf(TExp#(addrWidth)));
  return ifc;
endmodule

module mkBramGenVec
  #(function Vector#(n,dataT) gen(addrT addr)) (BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  let ifc <- mkSizedBramGenVec(valueOf(TExp#(addrWidth)), gen);
  return ifc;
endmodule

module mkBramInitVec#(Vector#(n,dataT) init) (BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  let ifc <- mkSizedBramInitVec(valueOf(TExp#(addrWidth)), init);
  return ifc;
endmodule

// This is a wrapper on Bram that allow to write using a mask (so it's not necessary to load
// the data first)
interface BramBE#(type addrT, numeric type dataW);
  method Action write(addrT addr, Bit#(dataW) data, Bit#(TDiv#(dataW,8)) mask);
  method Action read(addrT addr);
  method Bit#(dataW) response;
  method Bool canRead;
  method Bool canDeq;
  method Action deq;
endinterface

module wrapBramBE#(BRAM_DUAL_PORT_BE#(addrT,Bit#(dataW),TDiv#(dataW,8)) bram)
  (BramBE#(addrT, dataW)) provisos (Bits#(addrT, addrWidth), Eq#(addrT));

  FIFOF#(Tuple2#(Bit#(dataW), Bit#(TDiv#(dataW,8)))) rsp <- mkPipelineFIFOF;

  RWire#(addrT) currentWrAddr <- mkRWire;
  RWire#(Bit#(dataW)) currentWrData <- mkRWire;
  RWire#(Bit#(TDiv#(dataW,8))) currentWrMask <- mkRWire;
  let wrAddr = fromMaybe(?, currentWrAddr.wget);
  let wrData = fromMaybe(?, currentWrData.wget);
  let wrMask = fromMaybe(?, currentWrMask.wget);
  let wrValid = isJust(currentWrAddr.wget);

  RWire#(addrT) currentRdAddr <- mkRWire;
  let rdAddr = fromMaybe(?, currentRdAddr.wget);
  let rdValid = isJust(currentRdAddr.wget);

  (* no_implicit_conditions, fire_when_enabled *)
  rule block_ram_apply_write if (wrValid);
    bram.a.put(wrMask, wrAddr, wrData);
  endrule

  (* fire_when_enabled *)
  rule block_ram_apply_read if (rdValid && rsp.notFull());
    let data = tuple2(wrData, wrValid && wrAddr == rdAddr ? wrMask : 0);
    bram.b.put(0, rdAddr, ?);
    rsp.enq(data);
  endrule

  method Action write(addrT addr, Bit#(dataW) data, Bit#(TDiv#(dataW,8)) mask);
    currentWrAddr.wset(addr);
    currentWrData.wset(data);
    currentWrMask.wset(mask);
  endmethod

  method Action read(addrT addr) if (rsp.notFull());
    currentRdAddr.wset(addr);
  endmethod

  method Bool canRead = rsp.notFull;

  method Bit#(dataW) response if (rsp.notEmpty);
    Bit#(8) ret[valueOf(TDiv#(dataW,8))];
    match {.data, .mask} = rsp.first;

    for (Integer i=0; i < arrayLength(ret); i = i + 1) begin
      Bit#(8) rhs = bram.b.read[8*i+7:8*i];
      Bit#(8) lhs = data[8*i+7:8*i];

      ret[i] = mask[i] == 1 ? lhs : rhs;
    end

    return packArray(ret);
  endmethod

  method canDeq = rsp.notEmpty;

  method deq = rsp.deq;
endmodule

module mkSizedBramBE#(Integer size) (BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrSz), Eq#(addrT));
  BramVec#(addrT, TDiv#(dataW,8), Bit#(8)) bram <- mkSizedBramVec(size);

  method canDeq = bram.canDeq;
  method response = packArray(vectorToArray(bram.response));
  method canRead = bram.canRead;
  method read = bram.read;
  method deq = bram.deq;

  method Action write(addrT addr, Bit#(dataW) data, Bit#(TDiv#(dataW,8)) mask);
    action
      bram.write(addr, arrayToVector(unpackArray(data, valueof(dataW)/8)), mask);
    endaction
  endmethod
endmodule

module mkSizedBramGenBE
  #(Integer size, function Bit#(dataW) gen(addrT addr)) (BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrSz), Eq#(addrT));

  function Vector#(TDiv#(dataW,8), Bit#(8)) genVector(addrT a) =
    arrayToVector(unpackArray(gen(a), valueOf(dataW)/8));

  BramVec#(addrT, TDiv#(dataW,8), Bit#(8)) bram <-
    mkSizedBramGenVec(size, genVector);

  method canDeq = bram.canDeq;
  method response = packArray(vectorToArray(bram.response));
  method canRead = bram.canRead;
  method read = bram.read;
  method deq = bram.deq;

  method Action write(addrT addr, Bit#(dataW) data, Bit#(TDiv#(dataW,8)) mask);
    action
      bram.write(addr, arrayToVector(unpackArray(data, valueof(dataW)/8)), mask);
    endaction
  endmethod
endmodule

module mkSizedBramInitBE
  #(Integer size, Bit#(dataW) init) (BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT));
  let ifc <- mkSizedBramGenBE(size, constFn(init));
  return ifc;
endmodule

module mkBramBE(BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT));
  let ifc <- mkSizedBramBE(valueOf(TExp#(addrWidth)));
  return ifc;
endmodule

module mkBramGenBE#(function Bit#(dataW) gen(addrT addr))(BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT));
  let ifc <- mkSizedBramGenBE(valueOf(TExp#(addrWidth)), gen);
  return ifc;
endmodule

module mkBramInitBE#(Bit#(dataW) init) (BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT));
  let ifc <- mkSizedBramInitBE(valueOf(TExp#(addrWidth)), init);
  return ifc;
endmodule

// Return a vector of BlockRam using a uniq Block of RAM
module mkVectorBram#(Bram#(addrT, dataT) bram) (Vector#(n, Bram#(addrT, dataT)));
  Ehr#(2, Bit#(TLog#(n))) ehr <- mkEhr(?);

  Vector#(n, Bram#(addrT, dataT)) ret = newVector;

  for (Integer i=0; i < valueOf(n); i = i + 1) begin
    ret[i] = interface Bram;
      method Action read(addrT addr);
        action
          ehr[1] <= fromInteger(i);
          bram.read(addr);
        endaction
      endmethod

      method canRead = bram.canRead;

      method dataT response() if (ehr[0] == fromInteger(i));
        return bram.response();
      endmethod

      method Action deq() if (ehr[0] == fromInteger(i));
        bram.deq();
      endmethod

      method canDeq = ehr[0] == fromInteger(i) && bram.canDeq();

      method write = bram.write;
    endinterface;
  end

  return ret;
endmodule

// Return a vector of BlockRam using a uniq Block of RAM
module mkVectorBramBE#(BramBE#(addrT, dataW) bram) (Vector#(n, BramBE#(addrT, dataW)));
  Ehr#(2, Bit#(TLog#(n))) ehr <- mkEhr(?);

  Vector#(n, BramBE#(addrT, dataW)) ret = newVector;

  for (Integer i=0; i < valueOf(n); i = i + 1) begin
    ret[i] = interface BramBE;
      method Action read(addrT addr);
        action
          ehr[1] <= fromInteger(i);
          bram.read(addr);
        endaction
      endmethod

      method canRead = bram.canRead;

      method Bit#(dataW) response() if (ehr[0] == fromInteger(i));
        return bram.response();
      endmethod

      method canDeq = ehr[0] == fromInteger(i) && bram.canDeq();

      method Action deq() if (ehr[0] == fromInteger(i));
        bram.deq();
      endmethod

      method write = bram.write;
    endinterface;
  end

  return ret;
endmodule

// Return a vector of BlockRam using a uniq Block of RAM
module mkVectorBramVec#(BramVec#(addrT, m, dataT) bram)
  (Vector#(n, BramVec#(addrT, m, dataT)));
  Ehr#(2, Bit#(TLog#(n))) ehr <- mkEhr(?);

  Vector#(n, BramVec#(addrT, m, dataT)) ret = newVector;

  for (Integer i=0; i < valueOf(n); i = i + 1) begin
    ret[i] = interface BramVec;
      method Action read(addrT addr);
        action
          ehr[1] <= fromInteger(i);
          bram.read(addr);
        endaction
      endmethod

      method canRead = bram.canRead;

      method Vector#(m, dataT) response() if (ehr[0] == fromInteger(i));
        return bram.response();
      endmethod

      method canDeq = ehr[0] == fromInteger(i) && bram.canDeq();

      method Action deq() if (ehr[0] == fromInteger(i));
        bram.deq();
      endmethod

      method write = bram.write;
    endinterface;
  end

  return ret;
endmodule

module mkBramFromBramBE#(BramBE#(addrT, dataW) bram) (Bram#(addrT, Bit#(dataW)));
  method response = bram.response;
  method canRead = bram.canRead;
  method canDeq = bram.canDeq;
  method read = bram.read;
  method deq = bram.deq;

  method Action write(addrT addr, Bit#(dataW) data) =
    bram.write(addr, data, -1);
endmodule

module mkBramFromBramVec#(BramVec#(addrT, n, dataT) bram)
  (Bram#(addrT, Vector#(n, dataT)));
  method response = bram.response;
  method canRead = bram.canRead;
  method canDeq = bram.canDeq;
  method read = bram.read;
  method deq = bram.deq;

  method Action write(addrT addr, Vector#(n, dataT) data) =
    bram.write(addr, data, -1);
endmodule
