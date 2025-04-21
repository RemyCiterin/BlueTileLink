import Connectable :: *;
import Vector :: *;
import Utils :: *;
import Fifo :: *;

`include "TL.defines"

/*
This package define a subset of the message layer of the
TileLink C cache coherency protocol, this layer define
requests/responses to move cache blocks and their associated
permissions, and a few operations that a DMA controller can
use to read or write data without caching.
+---------------+---+---+---+---+---+-------------------------+
| Message       | A | B | C | D | E | Response                |
+---------------+---+---+---+---+---+-------------------------+
| AcquireBlock  | X | . | . | . | . | GrantData               |
| AcquirePerms  | X | . | . | . | . | Grant                   |
| GrantData     | . | . | . | X | . | GrantAck                |
| Grant         | . | . | . | X | . | GrantAck                |
| GrantAck      | . | . | . | . | X |                         |
+---------------+---+---+---+---+---+-------------------------+
| ProbeBlock    | . | X | . | . | . | ProbAck or ProbeAckData |
| ProbePerms    | . | X | . | . | . | ProbAck                 |
| ProbeAck      | . | . | X | . | . |                         |
| ProbeAckData  | . | . | X | . | . |                         |
+---------------+---+---+---+---+---+-------------------------+
| Release       | . | . | X | . | . | ReleaseAck              |
| ReleaseData   | . | . | X | . | . | ReleaseAck              |
| ReleaseAck    | . | . | . | X | . |                         |
+---------------+---+---+---+---+---+-------------------------+
| GetFull       | X | . | . | . | . | AccessAckData           |
| AccessAckData | . | . | . | X | . |                         |
+---------------+---+---+---+---+---+-------------------------+
| PutData       | X | . | . | . | . | AccessAck               |
| AccessAck     | . | . | . | X | . |                         |
+---------------+---+---+---+---+---+-------------------------+
*/

// Basic permissions as defined by the TileLink documentation
typedef enum {
  N = 2'd0, B = 2'd1, T = 2'd2
} TLPerm deriving(Bits, FShow, Eq);

instance Ord#(TLPerm);
    function Bool \< ( TLPerm x, TLPerm y );
        return pack(x) < pack(y);
    endfunction
    function Bool \<= ( TLPerm x, TLPerm y );
        return pack(x) <= pack(y);
    endfunction
    function Bool \> ( TLPerm x, TLPerm y );
        return pack(x) > pack(y);
    endfunction
    function Bool \>= ( TLPerm x, TLPerm y );
        return pack(x) >= pack(y);
    endfunction
    function Ordering compare( TLPerm x, TLPerm y );
        return compare(pack(x), pack(y));
    endfunction
    function TLPerm min( TLPerm x, TLPerm y );
        return x < y ? x : y;
    endfunction
    function TLPerm max( TLPerm x, TLPerm y );
        return x > y ? x : y;
    endfunction
endinstance

instance DefaultValue#(TLPerm);
  function TLPerm defaultValue = N;
endinstance

// Return if an agent have a read permission over a block
function Bool hasReadPerm(TLPerm perm);
  return perm > N;
endfunction

// Return if an agent have a write permissions over a block, note that this function
// for the `T` permission, the result is valid only if the node doesn't have branches
function Bool hasWritePerm(TLPerm perm);
  return perm > T;
endfunction

// Used by a cache block to acquire new permissions over a cache block
typedef enum {
  NtoB = 0,
  NtoT = 1,
  BtoT = 2
} Grow deriving(Bits, FShow, Eq);

// Combination of `Shrink` and `Report`, used to inform the cache controller that
// a cache decrease it's permission over a cache block
typedef enum {
  TtoB = 0,
  TtoN = 1,
  BtoN = 2,
  NtoN = 3,
  TtoT = 4,
  BtoB = 5
} Reduce deriving(Bits, FShow, Eq);

// Used by a cache manager to inform a cache that it must reduce it's permissions
// over a cache blocl
typedef enum {
  T = 0, B = 1, N = 2
} Cap deriving(Bits, FShow, Eq);

// Logical operations
typedef enum {
  XOR = 0,
  OR = 1,
  AND = 2,
  SWAP = 3
} TLLogical deriving(Bits, FShow, Eq);

// Arithmetic operations
typedef enum {
  MIN = 0,
  MAX = 1,
  MINU = 2,
  MAXU = 3,
  ADD = 4
} TLArithmetic deriving(Bits, FShow, Eq);

typedef union tagged {
  Grow AcquireBlock;
  Grow AcquirePerms;
  void PutData;
  void GetFull;
} OpcodeA deriving(Bits, FShow, Eq);

typedef union tagged {
  Cap ProbePerms;
  Cap ProbeBlock;
} OpcodeB deriving(Bits, FShow, Eq);

typedef union tagged {
  Reduce ProbeAck;
  Reduce ProbeAckData;
  Reduce Release;
  Reduce ReleaseData;
} OpcodeC deriving(Bits, FShow, Eq);

typedef union tagged {
  Cap Grant;
  Cap GrantData;
  void ReleaseAck;
  void AccessAckData;
  void AccessAck;
} OpcodeD deriving(Bits, FShow, Eq);

typedef enum {
  GrantAck
} OpcodeE deriving(Bits, FShow, Eq);

typedef struct {
  OpcodeA opcode;
  Bit#(sizeW) size;
  Bit#(sourceW) source;
  Bit#(addrW) address;
  Bit#(dataW) mask;
  Byte#(dataW) data;
} ChannelA#(`TL_ARGS_DECL) deriving(Bits, FShow, Eq);

typedef struct {
  OpcodeB opcode;
  Bit#(sizeW) size;
  Bit#(sourceW) source;
  Bit#(addrW) address;
} ChannelB#(`TL_ARGS_DECL) deriving(Bits, FShow, Eq);

typedef struct {
  OpcodeC opcode;
  Bit#(sizeW) size;
  Bit#(sourceW) source;
  Bit#(addrW) address;
  Byte#(dataW) data;
} ChannelC#(`TL_ARGS_DECL) deriving(Bits, FShow, Eq);

typedef struct {
  OpcodeD opcode;
  Bit#(sizeW) size;
  Bit#(sourceW) source;
  Bit#(sinkW) sink;
  Byte#(dataW) data;
} ChannelD#(`TL_ARGS_DECL) deriving(Bits, FShow, Eq);

typedef struct {
  OpcodeE opcode;
  Bit#(sinkW) sink;
} ChannelE#(`TL_ARGS_DECL) deriving(Bits, FShow, Eq);

interface TLSlave#(`TL_ARGS_DECL);
  interface FifoI#(ChannelA#(`TL_ARGS)) channelA;
  interface FifoO#(ChannelB#(`TL_ARGS)) channelB;
  interface FifoI#(ChannelC#(`TL_ARGS)) channelC;
  interface FifoO#(ChannelD#(`TL_ARGS)) channelD;
  interface FifoI#(ChannelE#(`TL_ARGS)) channelE;
endinterface

interface TLMaster#(`TL_ARGS_DECL);
  interface FifoO#(ChannelA#(`TL_ARGS)) channelA;
  interface FifoI#(ChannelB#(`TL_ARGS)) channelB;
  interface FifoO#(ChannelC#(`TL_ARGS)) channelC;
  interface FifoI#(ChannelD#(`TL_ARGS)) channelD;
  interface FifoO#(ChannelE#(`TL_ARGS)) channelE;
endinterface

instance Connectable#(TLSlave#(`TL_ARGS), TLMaster#(`TL_ARGS));
  module mkConnection
    #(TLSlave#(`TL_ARGS) slave, TLMaster#(`TL_ARGS) master)(Empty);
    mkConnection(master.channelA, slave.channelA);
    mkConnection(slave.channelB, master.channelB);
    mkConnection(master.channelC, slave.channelC);
    mkConnection(slave.channelD, master.channelD);
    mkConnection(master.channelE, slave.channelE);
  endmodule
endinstance

instance Connectable#(TLMaster#(`TL_ARGS), TLSlave#(`TL_ARGS));
  module mkConnection
    #(TLMaster#(`TL_ARGS) master, TLSlave#(`TL_ARGS) slave)(Empty);
    mkConnection(slave, master);
  endmodule
endinstance

function Bool hasDataA(OpcodeA opcode);
  return opcode == PutData;
endfunction

function Bool hasDataB(OpcodeB opcode);
  return False;
endfunction

function Bool hasDataC(OpcodeC opcode);
  return case (opcode) matches
    tagged ProbeAckData .* : True;
    tagged ReleaseData .* : True;
    default: False;
  endcase;
endfunction

function Bool hasDataD(OpcodeD opcode);
  return case (opcode) matches
    tagged GrantData .* : True;
    AccessAckData : True;
    default: False;
  endcase;
endfunction

function Bool hasDataE(OpcodeE opcode);
  return False;
endfunction

typedef Vector#(n,TLSlave#(`TL_ARGS)) VecTLSlave#(numeric type n,`TL_ARGS_DECL);

module mkVectorTLSlave#(TLSlave#(`TL_ARGS) slave) (Vector#(n, TLSlave#(`TL_ARGS)));
  Reg#(Bit#(addrW)) sizeA <- mkReg(0);
  Reg#(Bit#(addrW)) sizeC <- mkReg(0);
  Reg#(Bit#(TLog#(n))) stateA <- mkReg(0);
  Reg#(Bit#(TLog#(n))) stateC <- mkReg(0);

  Bit#(sizeW) logDataW = fromInteger(valueOf(TLog#(dataW)));

  Vector#(n, TLSlave#(`TL_ARGS)) ret = newVector;

  for (Integer i=0; i < valueOf(n); i = i + 1) begin
    ret[i] = interface TLSlave;
      interface FifoI channelA;
        method canEnq = (sizeA == 0 || fromInteger(i) == stateA) && slave.channelA.canEnq;

        method Action enq(ChannelA#(`TL_ARGS) msg)
          if (stateA == fromInteger(i) || sizeA == 0);
          action
            Bool first = sizeA == 0;
            Bool last =
              !hasDataA(msg.opcode) ||
              sizeA == fromInteger(valueOf(dataW)) ||
              (sizeA == 0 && logDataW >= msg.size);

            let size = first ? 1 << msg.size : sizeA;
            sizeA <= last ? 0 : size - fromInteger(valueOf(dataW));
            stateA <= fromInteger(i);

            slave.channelA.enq(msg);
          endaction
        endmethod
      endinterface

      interface FifoI channelC;
        method canEnq = (sizeC == 0 || fromInteger(i) == stateC) && slave.channelC.canEnq;

        method Action enq(ChannelC#(`TL_ARGS) msg)
          if (stateC == fromInteger(i) || sizeC == 0);
          action
            Bool first = sizeC == 0;
            Bool last =
              !hasDataC(msg.opcode) ||
              sizeC == fromInteger(valueOf(dataW)) ||
              (sizeC == 0 && logDataW >= msg.size);

            let size = first ? 1 << msg.size : sizeC;
            sizeC <= last ? 0 : size - fromInteger(valueOf(dataW));
            stateC <= fromInteger(i);

            slave.channelC.enq(msg);
          endaction
        endmethod
      endinterface

      interface channelB = slave.channelB;
      interface channelD = slave.channelD;
      interface channelE = slave.channelE;
    endinterface;
  end

  return ret;
endmodule

function TLPerm reduceTo(Reduce reduce);
  return case (reduce) matches
    TtoB : B;
    TtoN : N;
    BtoN : N;
    NtoN : N;
    TtoT : T;
    BtoB : B;
  endcase;
endfunction

function TLPerm reduceFrom(Reduce reduce);
  return case (reduce) matches
    TtoB : T;
    TtoN : T;
    BtoN : B;
    NtoN : N;
    TtoT : T;
    BtoB : B;
  endcase;
endfunction

// Permission needed to perform a channelA transaction
function TLPerm permChannelA(OpcodeA opcode);
  return case (opcode) matches
    tagged AcquirePerms BtoT : T;
    tagged AcquirePerms NtoT : T;
    tagged AcquirePerms NtoB : B;
    tagged AcquireBlock BtoT : T;
    tagged AcquireBlock NtoT : T;
    tagged AcquireBlock NtoB : B;
    PutData : T;
    GetFull : B;
  endcase;
endfunction
