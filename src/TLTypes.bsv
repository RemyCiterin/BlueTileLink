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
| GetAckData    | . | . | . | X | . |                         |
+---------------+---+---+---+---+---+-------------------------+
| PutData       | X | . | . | . | . | AccessAck               |
| PutAck        | . | . | . | X | . |                         |
+---------------+---+---+---+---+---+-------------------------+
*/

// Basic permissions as defined by the TileLink documentation
typedef enum {
  N = 2'd0, B = 2'd1, T = 2'd2
} PermTL deriving(Bits, FShow, Eq);

instance Ord#(PermTL);
    function Bool \< ( PermTL x, PermTL y );
        return pack(x) < pack(y);
    endfunction
    //function Bool \<= ( PermTL x, PermTL y );
    //    return pack(x) <= pack(y);
    //endfunction
    //function Bool \> ( PermTL x, PermTL y );
    //    return pack(x) > pack(y);
    //endfunction
    //function Bool \>= ( PermTL x, PermTL y );
    //    return pack(x) >= pack(y);
    //endfunction
    //function Ordering compare( PermTL x, PermTL y );
    //    return compare(pack(x), pack(y));
    //endfunction
    //function PermTL min( PermTL x, PermTL y );
    //    return x < y ? x : y;
    //endfunction
    //function PermTL max( PermTL x, PermTL y );
    //    return x > y ? x : y;
    //endfunction
endinstance

instance DefaultValue#(PermTL);
  function PermTL defaultValue = N;
endinstance

// Return if an agent have a read permission over a block
function Bool hasReadPerm(PermTL perm);
  return perm > N;
endfunction

// Return if an agent have a write permissions over a block, note that this function
// for the `T` permission, the result is valid only if the node doesn't have branches
function Bool hasWritePerm(PermTL perm);
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
  void PutAckData;
  void PutAck;
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

