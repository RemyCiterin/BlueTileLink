import RevertingVirtualReg :: *;
import RegFile :: *;

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

/* sub < write < forward */
module mkForwardRegFileFull(ForwardRegFile#(k,v))
  provisos(Bits#(k,sk),Bounded#(k),Bits#(v,sv),Eq#(k));
  Reg#(Bool) order <- mkRevertingVirtualReg(True);
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
      order <= False;
    endaction
  endmethod

  method v forward(k key);
    if (forwardKey.wget matches tagged Valid .x &&& x == key)
      return unJust(forwardVal.wget);
    else return regFile.sub(key);
  endmethod

  method sub = when(order, regFile.sub);
endmodule


module mkForwardRegFileFullInit#(a init) (ForwardRegFile#(Bit#(n), a)) provisos(Bits#(a, sa));
  Reg#(Bool) is_init <- mkReg(False);
  Reg#(Bit#(n)) idx <- mkReg(0);

  ForwardRegFile#(Bit#(n), a) rf <- mkForwardRegFileFull;

  rule init_register_file if (!is_init);
    rf.upd(idx, init);

    if (~idx == 0) is_init <= True;
    else idx <= idx + 1;
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
