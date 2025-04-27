import SpecialFIFOs :: *;
import RegFile :: *;
import Assert :: *;
import FIFOF :: *;

typedef Bit#(TLog#(n)) Token#(numeric type n);

typedef Bit#(TMul#(n,8)) Byte#(numeric type n);

instance StringLiteral#(Fmt);
  function Fmt fromString(String s) = $format("%s", s);
endinstance

function Action doAssert(Bool b, Fmt str);
  action
    if (!b) begin
      //`ifdef BSIM
      $fdisplay(stderr, "\n%m: ASSERT FAIL!!");
      $fdisplay(stderr, "\n", str);
      //`endif
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


// if x = {x[size-1], ..., x[0]}
// return {x[size-1-a], ..., x[0], x[size-1], ..., x[(size-a) % size]}
function Bit#(size) rotateLeft(Bit#(size) x, Bit#(TLog#(size)) a);
  // x = {x[size-1], ..., x[0]}
  // x << a = {x[size-1-a], ..., x[0], 0, ..., 0}
  // x >> b = {0, ..., 0, x[size-1], ..., x[b]}
  // And we want 1+(size-1-a) to be equal to b, so b=size-a

  if (valueOf(size) < 2) return x;
  else begin
    Bit#(TLog#(size)) b = fromInteger(valueOf(size) - 1) - a + 1;
    return (x << a) | (x >> b);
  end
endfunction

function Bit#(size) rotateRight(Bit#(size) x, Bit#(TLog#(size)) a);
  // x = {x[size-1], ..., x[0]}
  // x >> a = {0, ..., 0, x[size-1], ..., x[a]}
  // x << b = {x[size-1-b], ..., x[0], 0, ..., 0}
  // And we want 1+(size-1-b) to be equal to a, so b = size-a

  if (valueOf(size) < 2) return x;
  else begin
    Bit#(TLog#(size)) b = fromInteger(valueOf(size) - 1) - a + 1;
    return (x >> a) | (x << b);
  end
endfunction

// return the index of the less significant one
function Bit#(TAdd#(TLog#(size), 1)) firstOne(Bit#(size) x);

  function Bit#(TAdd#(TLog#(size), 1)) aux(Integer k);
    if (k == valueOf(size))
      return fromInteger(valueOf(size));
    else
      return x[k] == 1 ? fromInteger(k) : aux(k+1);
  endfunction

  return aux(0);
endfunction

// return the index of the most significant one
function Bit#(TAdd#(TLog#(size), 1)) lastOne(Bit#(size) x);

  function Bit#(TAdd#(TLog#(size), 1)) aux(Integer k);
    if (k == valueOf(size))
      return fromInteger(valueOf(size));
    else
      return x[valueOf(size) - 1 - k] == 1 ?
        fromInteger(valueOf(size) - 1 - k) :
        aux(k+1);
  endfunction

  return aux(0);
endfunction

// Return the index of the first one in a bitmask starting by a given index
function Maybe#(Bit#(TLog#(size)))
  firstOneFrom(Bit#(size) x, Bit#(TLog#(size)) n);

  let y = rotateRight(x, n);
  let m = firstOne(y);

  if (m == fromInteger(valueOf(size)))
    return Invalid;
  else begin
    let k = {1'b0, n} + m;
    return Valid(
      k >= fromInteger(valueOf(size)) ?
        truncate(k - fromInteger(valueOf(size))) :
        truncate(k)
    );
  end
endfunction

// Return the index of the last one in a bitmask starting by a given index
function Maybe#(Bit#(TLog#(size)))
  lastOneFrom(Bit#(size) x, Bit#(TLog#(size)) n);

  let y = rotateRight(x, n);
  let m = lastOne(y);

  if (m == fromInteger(valueOf(size)))
    return Invalid;
  else begin
    let k = {1'b0, n} + m;
    return Valid(
      k >= fromInteger(valueOf(size)) ?
        truncate(k - fromInteger(valueOf(size))) :
        truncate(k)
    );
  end
endfunction
