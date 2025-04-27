import FIFOF :: *;
import SpecialFIFOs :: *;
import BypassReg :: *;
import BRAMCore :: *;
import Vector :: *;
import Utils :: *;

import AXI4_Lite :: *;
import AXI4 :: *;

import Ehr :: *;


interface Bram#(type addrT, type dataT);
  method Action write(addrT addr, dataT data);
  method Action read(addrT addr);
  method dataT response;
  method Bool canRead;
  method Bool canDeq;
  method Action deq;
endinterface

module mkSizedBram#(Integer size) (Bram#(addrT, dataT))
  provisos (Bits#(addrT, addrWidth), Bits#(dataT, dataWidth), Eq#(addrT));
  BRAM_DUAL_PORT#(addrT, dataT) bram <- mkBRAMCore2(size, False);
  let wrPort = bram.a;
  let rdPort = bram.b;

  Ehr#(2, Maybe#(dataT)) rdData <- mkEhr(Invalid);
  Ehr#(2, Bool) valid <- mkEhr(False);
  Ehr#(2, addrT) rdAddr <- mkEhr(?);

  Wire#(Bool) wrValid <- mkDWire(False);
  Wire#(addrT) wrAddr <- mkDWire(?);
  Wire#(dataT) wrData <- mkDWire(?);

  (* no_implicit_conditions, fire_when_enabled *)
  rule block_ram_apply_write if (wrValid);
    wrPort.put(True, wrAddr, wrData);

    if (wrAddr == rdAddr[1])
      rdData[1] <= Valid(wrData);
  endrule

  method Action write(addrT addr, dataT data);
    wrValid <= True;
    wrAddr <= addr;
    wrData <= data;
  endmethod

  method Action read(addrT addr) if (!valid[1]);
    rdPort.put(False, addr, ?);
    rdData[0] <= Invalid;
    rdAddr[0] <= addr;
    valid[1] <= True;
  endmethod

  method Bool canRead = !valid[1];

  method dataT response if (valid[0]);
    case (rdData[0]) matches
      tagged Valid .data : return data;
      tagged Invalid: return rdPort.read;
    endcase
  endmethod

  method canDeq = valid[0];

  method Action deq if (valid[0]);
    action
      valid[0] <= False;
    endaction
  endmethod

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

module mkSizedBramVec#(Integer size) (BramVec#(addrT, n, dataT))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT), Bits#(dataT, dataW));
  Vector#(n, BRAM_DUAL_PORT#(addrT, dataT)) bram <-
    replicateM(mkBRAMCore2(size, False));

  Ehr#(2, addrT) rdAddr <- mkEhr(?);
  Ehr#(2, Bit#(n)) rdMask <- mkEhr(0);
  Reg#(Vector#(n,dataT)) rdData <- mkReg(?);
  Ehr#(2, Bool) valid <- mkEhr(False);

  Wire#(Bool) wrValid <- mkDWire(False);
  Wire#(Vector#(n,dataT)) wrData <- mkDWire(?);
  Wire#(Bit#(n)) wrMask <- mkDWire(?);
  Wire#(addrT) wrAddr <- mkDWire(?);

  (* no_implicit_conditions, fire_when_enabled *)
  rule block_ram_apply_write if (wrValid);
    for (Integer i=0; i < valueOf(n); i = i + 1) if (wrMask[i] == 1) begin
      bram[i].a.put(True, wrAddr, wrData[i]);
    end

    if (wrAddr == rdAddr[1]) begin
      rdMask[1] <= wrMask;
      rdData <= wrData;
    end
  endrule

  method Action write(addrT addr, Vector#(n, dataT) data, Bit#(n) mask);
    wrValid <= True;
    wrData <= data;
    wrMask <= mask;
    wrAddr <= addr;
  endmethod

  method Action read(addrT addr) if (!valid[1]);
    for (Integer i=0; i < valueOf(n); i = i + 1) begin
      bram[i].b.put(False, addr, ?);
    end

    rdAddr[0] <= addr;
    valid[1] <= True;
    rdMask[0] <= 0;
  endmethod

  method Bool canRead = !valid[1];

  method Vector#(n, dataT) response if (valid[0]);
    Vector#(n, dataT) ret = rdData;

    for (Integer i=0; i < valueOf(n); i = i + 1) begin
      if (rdMask[0][i] == 0) ret[i] = bram[i].b.read;
    end

    return ret;
  endmethod

  method canDeq = valid[0];

  method Action deq;
    action
      valid[0] <= False;
    endaction
  endmethod
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
  method Action write(addrT addr, Byte#(dataW) data, Bit#(dataW) mask);
  method Action read(addrT addr);
  method Byte#(dataW) response;
  method Bool canRead;
  method Bool canDeq;
  method Action deq;
endinterface

module mkSizedBramBE#(Integer size) (BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrSz), Eq#(addrT));
  BramVec#(addrT, dataW, Bit#(8)) bram <- mkSizedBramVec(size);

  method canDeq = bram.canDeq;
  method response = pack(bram.response);
  method canRead = bram.canRead;
  method read = bram.read;
  method deq = bram.deq;

  method Action write(addrT addr, Byte#(dataW) data, Bit#(dataW) mask);
    action
      bram.write(addr, unpack(data), mask);
    endaction
  endmethod
endmodule

module mkSizedBramGenBE
  #(Integer size, function Byte#(dataW) gen(addrT addr)) (BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrSz), Eq#(addrT));
  BramVec#(addrT, dataW, Bit#(8)) bram <- mkSizedBramGenVec(size, compose(unpack, gen));

  method canDeq = bram.canDeq;
  method response = pack(bram.response);
  method canRead = bram.canRead;
  method read = bram.read;
  method deq = bram.deq;

  method Action write(addrT addr, Byte#(dataW) data, Bit#(dataW) mask);
    action
      bram.write(addr, unpack(data), mask);
    endaction
  endmethod
endmodule

module mkSizedBramInitBE
  #(Integer size, Byte#(dataW) init) (BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT));
  let ifc <- mkSizedBramGenBE(size, constFn(init));
  return ifc;
endmodule

module mkBramBE(BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT));
  let ifc <- mkSizedBramBE(valueOf(TExp#(addrWidth)));
  return ifc;
endmodule

module mkBramGenBE#(function Byte#(dataW) gen(addrT addr))(BramBE#(addrT, dataW))
  provisos (Bits#(addrT, addrWidth), Eq#(addrT));
  let ifc <- mkSizedBramGenBE(valueOf(TExp#(addrWidth)), gen);
  return ifc;
endmodule

module mkBramInitBE#(Byte#(dataW) init) (BramBE#(addrT, dataW))
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

      method Byte#(dataW) response() if (ehr[0] == fromInteger(i));
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

module mkBramFromBramBE#(BramBE#(addrT, dataW) bram) (Bram#(addrT, Byte#(dataW)));
  method response = bram.response;
  method canRead = bram.canRead;
  method canDeq = bram.canDeq;
  method read = bram.read;
  method deq = bram.deq;

  method Action write(addrT addr, Byte#(dataW) data) =
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
