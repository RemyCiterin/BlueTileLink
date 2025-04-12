import SpecialFIFOs :: *;
import RegFile :: *;
import Assert :: *;
import FIFOF :: *;

typedef Bit#(TMul#(n,8)) Byte#(numeric type n);

instance StringLiteral#(Fmt);
  function Fmt fromString(String s) = $format("%s", s);
endinstance

function Action doAssert(Bool b, Fmt str);
  action
    if (!b) begin
      `ifndef BSIM
      $fdisplay(stderr, "\n%m: ASSERT FAIL!!");
      $fdisplay(stderr, "\n", str);
      `endif
      dynamicAssert(b, "");
    end
  endaction
endfunction

module mkRegFileFullInit#(a init) (RegFile#(Bit#(n), a)) provisos(Bits#(a, sa));
  Reg#(Bool) is_init <- mkReg(False);
  Reg#(Bit#(n)) idx <- mkReg(0);

  RegFile#(Bit#(n), a) rf <- mkRegFileFull;

  rule init_register_file if (!is_init);
    rf.upd(idx, init);

    if (~idx == 0)
      is_init <= True;
    else
      idx <= idx + 1;
  endrule

  method a sub(Bit#(n) index) if (is_init);
    return rf.sub(index);
  endmethod

  method Action upd(Bit#(n) index, a val) if (is_init);
    rf.upd(index, val);
  endmethod
endmodule

module mkRegFileFullGen#(function a init(Bit#(n) arg))
  (RegFile#(Bit#(n), a)) provisos(Bits#(a, sa));
  Reg#(Bool) is_init <- mkReg(False);
  Reg#(Bit#(n)) idx <- mkReg(0);

  RegFile#(Bit#(n), a) rf <- mkRegFileFull;

  rule init_register_file if (!is_init);
    rf.upd(idx, init(idx));

    if (~idx == 0)
      is_init <= True;
    else
      idx <= idx + 1;
  endrule

  method a sub(Bit#(n) index) if (is_init);
    return rf.sub(index);
  endmethod

  method Action upd(Bit#(n) index, a val) if (is_init);
    rf.upd(index, val);
  endmethod
endmodule

interface ForwardRegFile#(type k, type v);
  method Action upd(k key, v value);
  method v forward(k key);
  method v sub(k key);
endinterface

module mkForwardRegFileFull(ForwardRegFile#(k,v))
  provisos(Bits#(k,sk),Bounded#(k),Bits#(v,sv),Eq#(k));
  RegFile#(k,v) regFile <- mkRegFileFull;
  RWire#(k) forwardKey <- mkRWire;
  RWire#(v) forwardVal <- mkRWire;

  (* no_implicit_conditions, fire_when_enabled *)
  rule update_register_file
    if (forwardKey.wget matches tagged Valid .key);
      regFile.upd(key, unJust(forwardVal.wget));
  endrule

  // The write is delayed because forward depend of `regFile.sub` but
  // `regFile.sub < regFile.upd`
  method Action upd(k key, v val);
    action
      forwardKey.wset(key);
      forwardVal.wset(val);
    endaction
  endmethod

  method v forward(k key);
    if (forwardKey.wget matches tagged Valid .x &&& x == key)
      return unJust(forwardVal.wget);
    else return regFile.sub(key);
  endmethod

  method sub = regFile.sub;
endmodule


module mkForwardRegFileFullInit#(a init)
  (ForwardRegFile#(Bit#(n), a)) provisos(Bits#(a, sa));
  Reg#(Bool) is_init <- mkReg(False);
  Reg#(Bit#(n)) idx <- mkReg(0);

  ForwardRegFile#(Bit#(n), a) rf <- mkForwardRegFileFull;

  rule init_register_file if (!is_init);
    rf.upd(idx, init);

    if (~idx == 0)
      is_init <= True;
    else
      idx <= idx + 1;
  endrule

  method a sub(Bit#(n) index) if (is_init);
    return rf.sub(index);
  endmethod

  method a forward(Bit#(n) index) if (is_init);
    return rf.forward(index);
  endmethod

  method Action upd(Bit#(n) index, a val) if (is_init);
    rf.upd(index, val);
  endmethod
endmodule

module mkForwardRegFileFullGen#(function a init(Bit#(n) arg))
  (ForwardRegFile#(Bit#(n), a)) provisos(Bits#(a, sa));
  Reg#(Bool) is_init <- mkReg(False);
  Reg#(Bit#(n)) idx <- mkReg(0);

  ForwardRegFile#(Bit#(n), a) rf <- mkForwardRegFileFull;

  rule init_rf if (!is_init);
    rf.upd(idx, init(idx));

    if (~idx == 0)
      is_init <= True;
    else
      idx <= idx + 1;
  endrule

  method a sub(Bit#(n) index) if (is_init);
    return rf.sub(index);
  endmethod

  method a forward(Bit#(n) index) if (is_init);
    return rf.forward(index);
  endmethod

  method Action upd(Bit#(n) index, a val) if (is_init);
    rf.upd(index, val);
  endmethod
endmodule


typedef union tagged {
  Integer Normal;
  Integer Bypass;
  void Pipeline;
} FIFOF_Config;

module mkEmptyFIFOF(FIFOF#(t)) provisos(Bits#(t, k));
  method clear = noAction;

  method Action enq(t val) if (False);
    noAction;
  endmethod

  method Bool notEmpty;
    return False;
  endmethod

  method Bool notFull;
    return False;
  endmethod

  method Action deq if(False);
    noAction;
  endmethod

  method t first if (False);
    return ?;
  endmethod
endmodule

// align an address using the AXI4 convention: mask the strb
function Tuple2#(Bit#(addrBits), Bit#(dataBytes)) alignAddr(Bit#(addrBits) addr, Bit#(dataBytes) strb);
  Bit#(TSub#(addrBits, TLog#(dataBytes))) addr_truncate =
    addr[valueOf(addrBits)-1: valueOf(TLog#(dataBytes))];

  Bit#(TLog#(dataBytes)) offset =
    addr[valueOf(TLog#(dataBytes)) - 1 : 0];

  for (Integer i=0; i < valueOf(dataBytes); i = i + 1) begin
    strb[i] = strb[i] & (fromInteger(i) >= offset ? 1'b1 : 1'b0);
  end

  return Tuple2{fst: {addr_truncate, 0}, snd: strb};
endfunction

module mkConfigFIFOF#(FIFOF_Config conf) (FIFOF#(t)) provisos(Bits#(t, k));

  FIFOF#(t) fifo = ?;

  case (conf) matches
    tagged Normal .n : fifo <- mkSizedFIFOF(n);
    tagged Bypass .n : fifo <- mkSizedBypassFIFOF(n);
    tagged Pipeline  : fifo <- mkPipelineFIFOF;
  endcase

  method enq = fifo.enq;
  method deq = fifo.deq;
  method clear = fifo.clear;
  method notEmpty = fifo.notEmpty;
  method notFull = fifo.notFull;
  method first = fifo.first;

endmodule
