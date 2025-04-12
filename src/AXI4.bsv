package AXI4;

// This package define a minimalistic AXI4 interface for managing SDRAM

import Utils :: *;
import Connectable :: *;
import FIFOF :: *;
import GetPut :: *;
import SpecialFIFOs :: *;
import Clocks :: *;

typedef enum {
  OKAY = 2'b00,
  // EXOKAY = 2'b01 // no lowk command for SDRAM
  SLVERR = 2'b10,
  DECERR = 2'b11
} AXI4_Response
deriving(Bits, FShow, Eq);

instance DefaultValue#(AXI4_Response);
  function defaultValue;
    return OKAY;
  endfunction
endinstance

typedef enum {
  FIXED = 2'b00,
  INCR = 2'b01,
  WRAP = 2'b10
} AXI4_BurstType deriving(Bits, Eq, FShow);

instance DefaultValue#(AXI4_BurstType);
  function defaultValue;
    return FIXED;
  endfunction
endinstance

function Bit#(addrBits) axi4NextAddr(Integer dataBytes, Bit#(addrBits) addr, AXI4_BurstType burst, Bit#(8) length);

  // first: align the address according to the data width
  addr = addr & ~((1 << log2(dataBytes)) - 1);

  case (burst) matches
    FIXED: return addr;
    INCR: return addr + fromInteger(dataBytes);
    WRAP: begin
      Bit#(addrBits) next = addr + fromInteger(dataBytes);

      Integer capacity = case (length) matches
        0: dataBytes;
        1: 2 * dataBytes;
        3: 4 * dataBytes;
        7: 8 * dataBytes;
        15: 16 * dataBytes;
        default: dataBytes; // undefined behaviour
      endcase;

      if (next[log2(capacity)] == addr[log2(capacity)]) begin
        return next;
      end else begin
        for (Integer i=0; i < log2(capacity); i = i + 1) begin
          addr[i] = 0;
        end

        return addr;
      end
    end
  endcase
endfunction

typedef struct {
  Bit#(addrBits) addr; // data address
  Bit#(idBits) id; // id of the write request
  Bit#(8) length; // length of a burst
  AXI4_BurstType burst; // Type of burst: FIXED, INCR or WRAP
} AXI4_AWRequest#(numeric type idBits, numeric type addrBits) deriving(Bits, Eq, FShow);

typedef struct {
  Byte#(dataBytes) bytes; // data of the write request
  Bit#(dataBytes) strb; // strobe (mask) of the write request
  Bool last; // true if the data is the last of it's burst
} AXI4_WRequest#(numeric type dataBytes) deriving(Bits, Eq, FShow);

typedef struct {
  Bit#(idBits) id; // id of the request
  AXI4_Response resp; // status of the request
} AXI4_WResponse#(numeric type idBits) deriving(Bits, Eq, FShow);

typedef struct {
  Bit#(addrBits) addr; // data address
  Bit#(idBits) id; // id of the read request
  Bit#(8) length; // length of the burst
  AXI4_BurstType burst; // type of burst of the request: FIXED, INCR or WRAP
} AXI4_RRequest#(numeric type idBits, numeric type addrBits) deriving(Bits, Eq, FShow);

typedef struct {
  Bool last; // true if the response is the last of it's burst
  Byte#(dataBytes) bytes; // bytes of the burst element
  Bit#(idBits) id; // id of the request
  AXI4_Response resp; // status of the request
} AXI4_RResponse#(numeric type idBits, numeric type dataBytes) deriving(Bits, Eq, FShow);


 (* always_ready, always_enabled *)
 interface RdAXI4_Master_Fab#(numeric type idBits, numeric type addrBits, numeric type dataBytes);
   (* result= "arvalid"  *) method Bool arvalid;
   (* prefix= ""         *) method Action arready((* port= "arready" *) Bool a);
   (* result= "araddr"   *) method Bit#(addrBits) araddr;
   (* result= "arburst"  *) method AXI4_BurstType arburst;
   (* result= "arlength" *) method Bit#(8) arlength;
   (* result= "arid"     *) method Bit#(idBits) arid;

   (* result= "rready" *) method Bool rready;
   (* prefix= ""       *) method Action rvalid((* port="rvalid" *) Bool v);
   (* prefix= ""       *) method Action rdata((* port="rdata" *) Byte#(dataBytes) d);
   (* prefix= ""       *) method Action rlast((* port="rlast" *) Bool d);
   (* prefix= ""       *) method Action rid((* port="rid" *) Bit#(idBits) d);
   (* prefix= ""       *) method Action rresp((* port="rresp" *) AXI4_Response resp);
 endinterface

(* always_ready, always_enabled *)
interface RdAXI4_Slave_Fab#(numeric type idBits, numeric type addrBits, numeric type dataBytes);
  (* result= "arready" *) method Bool arready;
  (* prefix=""         *) method Action arvalid((* port="arvalid" *) Bool arvalid);
  (* prefix=""         *) method Action araddr((* port="araddr" *) Bit#(addrBits) a);
  (* prefix=""         *) method Action arburst((* port="arburst" *) AXI4_BurstType b);
  (* prefix=""         *) method Action arlength((* port="arlength" *) Bit#(8) l);
  (* prefix=""         *) method Action arid((* port="arid" *) Bit#(idBits) id);

  (* result= "rvalid" *) method Bool rvalid;
  (* prefix= ""       *) method Action rready((* port="rready" *)Bool rready);
  (* result= "rdata"  *) method Byte#(dataBytes) rdata();
  (* result= "rdata"  *) method Bool rlast();
  (* result= "rdata"  *) method Bit#(idBits) rid();
  (* result= "rresp"  *) method AXI4_Response rresp();
endinterface

instance Connectable#(RdAXI4_Slave_Fab#(i, a, d), RdAXI4_Master_Fab#(i, a, d));
  module mkConnection#(RdAXI4_Slave_Fab#(i, a, d) slave, RdAXI4_Master_Fab#(i, a, d) master)(Empty);
    rule arvalid; slave.arvalid(master.arvalid); endrule
    rule arready; master.arready(slave.arready); endrule
    rule araddr; slave.araddr(master.araddr); endrule
    rule arburst; slave.arburst(master.arburst); endrule
    rule arlength; slave.arlength(master.arlength); endrule
    rule arid; slave.arid(master.arid); endrule

    rule rready; slave.rready(master.rready); endrule
    rule rvalid; master.rvalid(slave.rvalid); endrule
    rule rdata; master.rdata(slave.rdata); endrule
    rule rlast; master.rlast(slave.rlast); endrule
    rule rid; master.rid(slave.rid); endrule
    rule rresp; master.rresp(slave.rresp); endrule
  endmodule
endinstance

instance Connectable#(RdAXI4_Master_Fab#(i, a, d), RdAXI4_Slave_Fab#(i, a, d));
  module mkConnection#(RdAXI4_Master_Fab#(i, a, d) master, RdAXI4_Slave_Fab#(i, a, d) slave)(Empty);
    mkConnection(slave, master);
  endmodule
endinstance

interface RdAXI4_Master#(numeric type i, numeric type a, numeric type d);
  interface Get#(AXI4_RRequest#(i, a)) request;
  interface Put#(AXI4_RResponse#(i, d)) response;
endinterface

interface RdAXI4_Slave#(numeric type i, numeric type a, numeric type d);
  interface Put#(AXI4_RRequest#(i, a)) request;
  interface Get#(AXI4_RResponse#(i, d)) response;
endinterface

instance Connectable#(RdAXI4_Slave#(i, a, d), RdAXI4_Master#(i, a, d));
  module mkConnection#(RdAXI4_Slave#(i, a, d) slave, RdAXI4_Master#(i, a, d) master)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.request, master.request);
  endmodule
endinstance

instance Connectable#(RdAXI4_Master#(i, a, d), RdAXI4_Slave#(i, a, d));
  module mkConnection#(RdAXI4_Master#(i, a, d) master, RdAXI4_Slave#(i, a, d) slave)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.request, master.request);
  endmodule
endinstance

(* always_ready, always_enabled *)
interface WrAXI4_Master_Fab#(numeric type idBits, numeric type addrBits, numeric type dataBytes);
  (* prefix= ""         *) method Action awready((* port="awready" *) Bool r);
  (* result= "awvalid"  *) method Bool awvalid;
  (* result= "awaddr"   *) method Bit#(addrBits) awaddr;
  (* result= "awburst"  *) method AXI4_BurstType awburst;
  (* result= "awlength" *) method Bit#(8) awlength;
  (* result= "awid"     *) method Bit#(idBits) awid;

  (* prefix= ""       *) method Action wready((* port="wready" *)Bool r);
  (* prefix= "wvalid" *) method Bool wvalid;
  (* prefix= "wdata"  *) method Byte#(dataBytes) wdata;
  (* prefix= "wstrb"  *) method Bit#(dataBytes) wstrb;
  (* prefix= "wlast"  *) method Bool wlast;

  (* prefix= ""       *) method Action bvalid((* port="bvalid" *) Bool b);
  (* result= "bready" *) method Bool bready;
  (* prefix= ""       *) method Action bresp((* port="bresp" *) AXI4_Response r);
  (* prefix= ""       *) method Action bid((* port="bid" *) Bit#(idBits) r);
endinterface

(* always_ready, always_enabled *)
interface WrAXI4_Slave_Fab#(numeric type idBits, numeric type addrBits, numeric type dataBytes);
  (* result= "awready" *) method Bool awready;
  (* prefix=""         *) method Action awvalid((* port="awvalid" *) Bool awvalid);
  (* prefix=""         *) method Action awaddr((* port="awaddr" *) Bit#(addrBits) a);
  (* prefix=""         *) method Action awburst((* port="awburst" *) AXI4_BurstType b);
  (* prefix=""         *) method Action awlength((* port="awlength" *) Bit#(8) l);
  (* prefix=""         *) method Action awid((* port="awid" *) Bit#(idBits) id);

  (* result= "wready" *) method Bool wready;
  (* prefix=""        *) method Action wvalid((* port="wvalid" *) Bool wvalid);
  (* prefix=""        *) method Action wdata((* port="wdata" *) Byte#(dataBytes) d);
  (* prefix=""        *) method Action wstrb((* port="wstrb" *) Bit#(dataBytes) s);
  (* prefix=""        *) method Action wlast((* port="wlast" *) Bool l);

  (* result= "bvalid" *) method Bool bvalid;
  (* prefix=""        *) method Action bready((* port="bready" *) Bool b);
  (* result= "bresp"  *) method AXI4_Response bresp();
  (* result= "bid"    *) method Bit#(idBits) bid();
endinterface

instance Connectable#(WrAXI4_Slave_Fab#(i, a, d), WrAXI4_Master_Fab#(i, a, d));
  module mkConnection#(WrAXI4_Slave_Fab#(i, a, d) slave, WrAXI4_Master_Fab#(i, a, d) master)(Empty);
    rule awready; master.awready(slave.awready); endrule
    rule awvalid; slave.awvalid(master.awvalid); endrule
    rule awaddr; slave.awaddr(master.awaddr); endrule
    rule awburst; slave.awburst(master.awburst); endrule
    rule awlength; slave.awlength(master.awlength); endrule
    rule awid; slave.awid(master.awid); endrule

    rule wready; master.wready(slave.wready); endrule
    rule wvalid; slave.wvalid(master.wvalid); endrule
    rule wdata; slave.wdata(master.wdata); endrule
    rule wstrb; slave.wstrb(master.wstrb); endrule
    rule wlast; slave.wlast(master.wlast); endrule

    rule bvalid; master.bvalid(slave.bvalid); endrule
    rule bready; slave.bready(master.bready); endrule
    rule bresp; master.bresp(slave.bresp); endrule
    rule bid; master.bid(slave.bid); endrule
  endmodule
endinstance

instance Connectable#(WrAXI4_Master_Fab#(i, a, d), WrAXI4_Slave_Fab#(i, a, d));
  module mkConnection#(WrAXI4_Master_Fab#(i, a, d) master, WrAXI4_Slave_Fab#(i, a, d) slave)(Empty);
    mkConnection(slave, master);
  endmodule
endinstance

interface WrAXI4_Master#(numeric type i, numeric type a, numeric type d);
  interface Get#(AXI4_WRequest#(d)) wrequest;
  interface Get#(AXI4_AWRequest#(i, a)) awrequest;
  interface Put#(AXI4_WResponse#(i)) response;
endinterface

interface WrAXI4_Slave#(numeric type i, numeric type a, numeric type d);
  interface Put#(AXI4_WRequest#(d)) wrequest;
  interface Put#(AXI4_AWRequest#(i, a)) awrequest;
  interface Get#(AXI4_WResponse#(i)) response;
endinterface

instance Connectable#(WrAXI4_Slave#(i, a, d), WrAXI4_Master#(i, a, d));
  module mkConnection#(WrAXI4_Slave#(i, a, d) slave, WrAXI4_Master#(i, a, d) master)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.awrequest, master.awrequest);
    mkConnection(slave.wrequest, master.wrequest);
  endmodule
endinstance

instance Connectable#(WrAXI4_Master#(i, a, d), WrAXI4_Slave#(i, a, d));
  module mkConnection#(WrAXI4_Master#(i, a, d) master, WrAXI4_Slave#(i, a, d) slave)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.awrequest, master.awrequest);
    mkConnection(slave.wrequest, master.wrequest);
  endmodule
endinstance

// Provide a master AXI4 interface, and a slave interface to send data to it using FIFOs
interface RdAXI4_Master_IFC#(numeric type i, numeric type a, numeric type d);
  (* prefix= "" *) interface RdAXI4_Master_Fab#(i, a, d) fabric;
  interface RdAXI4_Slave#(i, a, d) server;
endinterface

// Provide a slave AXI4 interface, and a master interface to receive data from it using FIFOs
interface RdAXI4_Slave_IFC#(numeric type i, numeric type a, numeric type d);
  (* prefix= "" *) interface RdAXI4_Slave_Fab#(i, a, d) fabric;
  interface RdAXI4_Master#(i, a, d) client;
endinterface

// Provide a master AXI4 interface, and a slave interface to send data to it using FIFOs
interface WrAXI4_Master_IFC#(numeric type i, numeric type a, numeric type d);
  (* prefix= "" *) interface WrAXI4_Master_Fab#(i, a, d) fabric;
  interface WrAXI4_Slave#(i, a, d) server;
endinterface

// Provide a slave AXI4 interface, and a master interface to receive data from it using FIFOs
interface WrAXI4_Slave_IFC#(numeric type i, numeric type a, numeric type d);
  (* prefix= "" *) interface WrAXI4_Slave_Fab#(i, a, d) fabric;
  interface WrAXI4_Master#(i, a, d) client;
endinterface

// conversion between read master `fabric` and `fifof` interfaces
module mkRdAXI4_Master#(FIFOF_Config conf) (RdAXI4_Master_IFC#(i, a, d));
  FIFOF#(AXI4_RRequest#(i, a)) request <- mkConfigFIFOF(conf);
  FIFOF#(AXI4_RResponse#(i, d)) response <- mkConfigFIFOF(conf);

  let isRst <- isResetAsserted();

  Wire#(Bool)           wire_arvalid  <- mkBypassWire();
  Wire#(Bool)           wire_arready  <- mkBypassWire();
  Wire#(Bit#(a))        wire_araddr   <- mkBypassWire();
  Wire#(AXI4_BurstType) wire_arburst  <- mkBypassWire();
  Wire#(Bit#(8))        wire_arlength <- mkBypassWire();
  Wire#(Bit#(i))        wire_arid     <- mkBypassWire();

  Wire#(Bool)          wire_rvalid <- mkBypassWire();
  Wire#(Bool)          wire_rready <- mkBypassWire();
  Wire#(Byte#(d))      wire_rdata  <- mkBypassWire();
  Wire#(Bit#(i))       wire_rid    <- mkBypassWire();
  Wire#(Bool)          wire_rlast  <- mkBypassWire();
  Wire#(AXI4_Response) wire_rresp  <- mkBypassWire();

  rule step;
    if (request.notEmpty() && !isRst) begin
      wire_arvalid <= True;
      wire_araddr <= request.first().addr;
      wire_arburst <= request.first().burst;
      wire_arlength <= request.first().length;
      wire_arid <= request.first().id;
      if (wire_arready) request.deq();
    end else begin
      wire_arvalid <= False;
      wire_arid <= 0;
      wire_arburst <= defaultValue;
      wire_arlength <= 0;
      wire_araddr <= 0;
    end

    wire_rready <= response.notFull() && !isRst;
    if (wire_rvalid && response.notFull() && !isRst) begin
      response.enq(AXI4_RResponse{bytes: wire_rdata, resp: wire_rresp, id: wire_rid, last: wire_rlast});
    end
  endrule

  interface RdAXI4_Slave server;
    interface request = toPut(request);
    interface response = toGet(response);
  endinterface

  interface RdAXI4_Master_Fab fabric;
    interface arready = wire_arready._write;
    interface arvalid = wire_arvalid;
    interface araddr = wire_araddr;
    interface arburst = wire_arburst;
    interface arlength = wire_arlength;
    interface arid = wire_arid;

    interface rready = wire_rready;
    interface rvalid = wire_rvalid._write;
    interface rdata = wire_rdata._write;
    interface rlast = wire_rlast._write;
    interface rid = wire_rid._write;
    interface rresp = wire_rresp._write;
  endinterface
endmodule

// conversion between read slave `fabric` and `fifof` interfaces
module mkRdAXI4_Slave#(FIFOF_Config conf) (RdAXI4_Slave_IFC#(i, a, d));
  FIFOF#(AXI4_RRequest#(i, a)) request <- mkConfigFIFOF(conf);
  FIFOF#(AXI4_RResponse#(i, d)) response <- mkConfigFIFOF(conf);

  let isRst <- isResetAsserted();

  Wire#(Bool)           wire_arvalid  <- mkBypassWire();
  Wire#(Bool)           wire_arready  <- mkBypassWire();
  Wire#(Bit#(a))        wire_araddr   <- mkBypassWire();
  Wire#(AXI4_BurstType) wire_arburst  <- mkBypassWire();
  Wire#(Bit#(8))        wire_arlength <- mkBypassWire();
  Wire#(Bit#(i))        wire_arid     <- mkBypassWire();

  Wire#(Bool)          wire_rvalid <- mkBypassWire();
  Wire#(Bool)          wire_rready <- mkBypassWire();
  Wire#(Byte#(d))      wire_rdata  <- mkBypassWire();
  Wire#(Bit#(i))       wire_rid    <- mkBypassWire();
  Wire#(Bool)          wire_rlast  <- mkBypassWire();
  Wire#(AXI4_Response) wire_rresp  <- mkBypassWire();

  rule step;
    if (request.notFull() && !isRst) begin
      wire_arready <= True;
      if (wire_arvalid)
        request.enq(AXI4_RRequest{addr:wire_araddr, burst: wire_arburst, length: wire_arlength, id: wire_arid});
    end else begin
      wire_arready <= False;
    end

    if (response.notEmpty() && !isRst) begin
      wire_rvalid <= True;
      wire_rdata <= response.first().bytes;
      wire_rresp <= response.first().resp;
      wire_rlast <= response.first().last;
      wire_rid <= response.first().id;
      if (wire_rready) response.deq();
    end else begin
      wire_rvalid <= False;
      wire_rdata <= 0;
      wire_rresp <= OKAY;
      wire_rlast <= False;
      wire_rid <= 0;
    end
  endrule

  interface RdAXI4_Master client;
    interface request = toGet(request);
    interface response = toPut(response);
  endinterface

  interface RdAXI4_Slave_Fab fabric;
    interface arready = wire_arready;
    interface arvalid = wire_arvalid._write;
    interface araddr = wire_araddr._write;
    interface arburst = wire_arburst._write;
    interface arlength = wire_arlength._write;
    interface arid = wire_arid._write;

    interface rready = wire_rready._write;
    interface rvalid = wire_rvalid;
    interface rdata = wire_rdata;
    interface rresp = wire_rresp;
    interface rlast = wire_rlast;
    interface rid = wire_rid;
  endinterface
endmodule



// conversion between read master `fabric` and `fifof` interfaces
module mkWrAXI4_Master#(FIFOF_Config conf) (WrAXI4_Master_IFC#(i, a, d));
  FIFOF#(AXI4_AWRequest#(i, a)) awrequest <- mkConfigFIFOF(conf);
  FIFOF#(AXI4_WRequest#(d)) wrequest <- mkConfigFIFOF(conf);

  FIFOF#(AXI4_WResponse#(i)) response <- mkConfigFIFOF(conf);

  let isRst <- isResetAsserted();

  Wire#(Bool)           wire_awready  <- mkBypassWire;
  Wire#(Bool)           wire_awvalid  <- mkBypassWire;
  Wire#(Bit#(a))        wire_awaddr   <- mkBypassWire;
  Wire#(AXI4_BurstType) wire_awburst  <- mkBypassWire;
  Wire#(Bit#(8))        wire_awlength <- mkBypassWire;
  Wire#(Bit#(i))        wire_awid     <- mkBypassWire;

  Wire#(Bool)     wire_wready <- mkBypassWire;
  Wire#(Bool)     wire_wvalid <- mkBypassWire;
  Wire#(Byte#(d)) wire_wdata  <- mkBypassWire;
  Wire#(Bit#(d))  wire_wstrb  <- mkBypassWire;
  Wire#(Bool)     wire_wlast  <- mkBypassWire;

  Wire#(Bool)          wire_bready <- mkBypassWire;
  Wire#(Bool)          wire_bvalid <- mkBypassWire;
  Wire#(AXI4_Response) wire_bresp  <- mkBypassWire;
  Wire#(Bit#(i))       wire_bid    <- mkBypassWire;


  rule step;
    // send address
    if (!isRst && awrequest.notEmpty()) begin
      wire_awvalid <= True;
      wire_awaddr <= awrequest.first().addr;
      wire_awburst <= awrequest.first().burst;
      wire_awlength <= awrequest.first().length;
      wire_awid <= awrequest.first().id;
      if (wire_awready) awrequest.deq();
    end else begin
      wire_awvalid <= False;
      wire_awaddr <= 0;
      wire_awburst <= defaultValue;
      wire_awlength <= 0;
      wire_awid <= 0;
    end

    // send data
    if (!isRst && wrequest.notEmpty()) begin
      wire_wvalid <= True;
      wire_wdata <= wrequest.first().bytes;
      wire_wstrb <= wrequest.first().strb;
      wire_wlast <= wrequest.first().last;
      if (wire_wready) wrequest.deq();
    end else begin
      wire_wvalid <= False;
      wire_wdata <= 0;
      wire_wstrb <= 15;
      wire_wlast <= True;
    end

    // receive response
    wire_bready <= !isRst && response.notFull();
    if (!isRst && response.notFull() && wire_bvalid) begin
      response.enq(AXI4_WResponse{resp: wire_bresp, id: wire_bid});
    end
  endrule

  interface WrAXI4_Slave server;
    interface wrequest = toPut(wrequest);
    interface awrequest = toPut(awrequest);
    interface response = toGet(response);
  endinterface

  interface WrAXI4_Master_Fab fabric;
    interface awready = wire_awready._write;
    interface awvalid = wire_awvalid;
    interface awaddr = wire_awaddr;
    interface awburst = wire_awburst;
    interface awlength = wire_awlength;
    interface awid = wire_awid;

    interface wready = wire_wready._write;
    interface wvalid = wire_wvalid;
    interface wdata = wire_wdata;
    interface wstrb = wire_wstrb;
    interface wlast = wire_wlast;

    interface bready = wire_bready;
    interface bvalid = wire_bvalid._write;
    interface bresp = wire_bresp._write;
    interface bid = wire_bid._write;
  endinterface
endmodule

// conversion between read master `fabric` and `fifof` interfaces
module mkWrAXI4_Slave#(FIFOF_Config conf) (WrAXI4_Slave_IFC#(i, a, d));
  FIFOF#(AXI4_AWRequest#(i, a)) awrequest <- mkConfigFIFOF(conf);
  FIFOF#(AXI4_WRequest#(d)) wrequest <- mkConfigFIFOF(conf);

  FIFOF#(AXI4_WResponse#(i)) response <- mkConfigFIFOF(conf);

  let isRst <- isResetAsserted();

  Wire#(Bool)           wire_awready  <- mkBypassWire;
  Wire#(Bool)           wire_awvalid  <- mkBypassWire;
  Wire#(Bit#(a))        wire_awaddr   <- mkBypassWire;
  Wire#(AXI4_BurstType) wire_awburst  <- mkBypassWire;
  Wire#(Bit#(8))        wire_awlength <- mkBypassWire;
  Wire#(Bit#(i))        wire_awid     <- mkBypassWire;

  Wire#(Bool)     wire_wready <- mkBypassWire;
  Wire#(Bool)     wire_wvalid <- mkBypassWire;
  Wire#(Byte#(d)) wire_wdata  <- mkBypassWire;
  Wire#(Bit#(d))  wire_wstrb  <- mkBypassWire;
  Wire#(Bool)     wire_wlast  <- mkBypassWire;

  Wire#(Bool)          wire_bready <- mkBypassWire;
  Wire#(Bool)          wire_bvalid <- mkBypassWire;
  Wire#(AXI4_Response) wire_bresp  <- mkBypassWire;
  Wire#(Bit#(i))       wire_bid    <- mkBypassWire;

  rule step;
    // receive address
    if (!isRst && awrequest.notFull()) begin
      wire_awready <= True;
      if (wire_awvalid)
        awrequest.enq(
          AXI4_AWRequest{
            addr: wire_awaddr,
            burst: wire_awburst,
            length: wire_awlength,
            id: wire_awid
          }
        );
    end else begin
      wire_awready <= False;
    end

    // receive data
    if (!isRst && wrequest.notFull()) begin
      wire_wready <= True;
      if (wire_wvalid)
        wrequest.enq(AXI4_WRequest{bytes: wire_wdata, strb: wire_wstrb, last: wire_wlast});
    end else begin
      wire_wready <= False;
    end

    // send response
    if (!isRst && response.notEmpty()) begin
      wire_bvalid <= True;
      wire_bresp <= response.first().resp;
      wire_bid <= response.first().id;
      if (wire_bready) response.deq();
    end else begin
      wire_bvalid <= False;
      wire_bresp <= OKAY;
      wire_bid <= 0;
    end
  endrule

  interface WrAXI4_Master client;
    interface wrequest = toGet(wrequest);
    interface awrequest = toGet(awrequest);
    interface response = toPut(response);
  endinterface

  interface WrAXI4_Slave_Fab fabric;
    interface awready = wire_awready;
    interface awvalid = wire_awvalid._write;
    interface awaddr = wire_awaddr._write;
    interface awburst = wire_awburst._write;
    interface awlength = wire_awlength._write;
    interface awid = wire_awid._write;

    interface wready = wire_wready;
    interface wvalid = wire_wvalid._write;
    interface wdata = wire_wdata._write;
    interface wstrb = wire_wstrb._write;
    interface wlast = wire_wlast._write;

    interface bready = wire_bready._write;
    interface bvalid = wire_bvalid;
    interface bresp = wire_bresp;
    interface bid = wire_bid;
  endinterface
endmodule

module mkEmptyWrAXI4_Master(WrAXI4_Master#(idBits, addrBits, dataBytes));
  FIFOF#(AXI4_AWRequest#(idBits, addrBits)) awrequest_fifo <- mkEmptyFIFOF;
  FIFOF#(AXI4_WRequest#(dataBytes)) wrequest_fifo <- mkEmptyFIFOF;
  FIFOF#(AXI4_WResponse#(idBits)) response_fifo <- mkEmptyFIFOF;

  interface awrequest = toGet(awrequest_fifo);
  interface wrequest = toGet(wrequest_fifo);
  interface response = toPut(response_fifo);
endmodule

module mkEmptyWrAXI4_Slave(WrAXI4_Slave#(idBits, addrBits, dataBytes));
  FIFOF#(AXI4_AWRequest#(idBits, addrBits)) awrequest_fifo <- mkEmptyFIFOF;
  FIFOF#(AXI4_WRequest#(dataBytes)) wrequest_fifo <- mkEmptyFIFOF;
  FIFOF#(AXI4_WResponse#(idBits)) response_fifo <- mkEmptyFIFOF;

  interface awrequest = toPut(awrequest_fifo);
  interface wrequest = toPut(wrequest_fifo);
  interface response = toGet(response_fifo);
endmodule

module mkEmptyRdAXI4_Master(RdAXI4_Master#(idBits, addrBits, dataBytes));
  FIFOF#(AXI4_RRequest#(idBits, addrBits)) request_fifo <- mkEmptyFIFOF;
  FIFOF#(AXI4_RResponse#(idBits, dataBytes)) response_fifo <- mkEmptyFIFOF;

  interface request = toGet(request_fifo);
  interface response = toPut(response_fifo);
endmodule

module mkEmptyRdAXI4_Slave(RdAXI4_Slave#(idBits, addrBits, dataBytes));
  FIFOF#(AXI4_RRequest#(idBits, addrBits)) request_fifo <- mkEmptyFIFOF;
  FIFOF#(AXI4_RResponse#(idBits, dataBytes)) response_fifo <- mkEmptyFIFOF;

  interface request = toPut(request_fifo);
  interface response = toGet(response_fifo);
endmodule

endpackage
