import Vector :: *;
import Utils :: *;

/*
A "lane" is the unit of data in a TileLink message, a lane is a set of
"w" bytes (with "w" a power of two between 1 and 4096), and each message
will use a subset of the lane (or multiple lanes) to transport it's data
Each message contain a "size" field, an address field aligned on
"2^size", and a lane.

The lane always represent the data from the address "address & ~(w-1)"
to the address "(address & ~(w-1)) + w - 1" so the data element
transported in the message start at the offset "address & (w - 1)"
in the lane and contain "2^size" bytes.
*/

// "size" and "w" must be power of two with "size" divide "w"
function Byte#(size) getData(Bit#(a) addr, Byte#(w) lane)
  provisos(Mul#(size, wordPerLane, w));
  Vector#(wordPerLane, Byte#(size)) v = unpack(lane);
  Bit#(a) offset = addr & fromInteger(valueOf(w)-1);
  return v[offset >> valueOf(TLog#(size))];
endfunction

// "size" and "w" must be power of two with "size" divide "w"
function Byte#(w) getLane(Bit#(a) addr, Byte#(size) data)
  provisos(Mul#(size, wordPerLane, w));
  Bit#(a) offset = addr & fromInteger(valueOf(w)-1);
  Vector#(wordPerLane, Byte#(size)) lane = replicate(0);
  lane[offset >> valueOf(TLog#(size))] = data;
  return pack(lane);
endfunction

// "size" and "w" must be power of two with "size" divide "w"
function Bit#(size) getDataMask(Bit#(a) addr, Bit#(w) laneMask)
  provisos(Mul#(size, wordPerLane, w));
  Vector#(wordPerLane, Bit#(size)) v = unpack(laneMask);
  Bit#(a) offset = addr & fromInteger(valueOf(w)-1);
  return v[offset >> valueOf(TLog#(size))];
endfunction

// "size" and "w" must be power of two with "size" divide "w"
function Bit#(w) getLaneMask(Bit#(a) addr, Bit#(size) dataMask)
  provisos(Mul#(size, wordPerLane, w));
  Bit#(a) offset = addr & fromInteger(valueOf(w)-1);
  Vector#(wordPerLane, Bit#(size)) laneMask = replicate(0);
  laneMask[offset >> valueOf(TLog#(size))] = dataMask;
  return pack(laneMask);
endfunction

// Return the full mask for a given size (here size is the log of the beat size)
// Expect that `2^sizeW - 1 >= w`, otherwise it will generate a comptime error
function Bit#(w) getFullLaneMask(Bit#(a) addr, Bit#(sizeW) size);
  Bit#(a) offset = addr & fromInteger(valueOf(w)-1);
  Bit#(TExp#(sizeW)) width = 1 << size;

  if (width >= fromInteger(valueOf(w))) return ~0;
  else begin
    Bit#(w) mask = (1 << width) - 1;
    return mask << offset;
  end
endfunction
