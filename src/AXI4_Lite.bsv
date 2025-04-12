package AXI4_Lite;

import Utils :: *;
import Connectable :: *;
import FIFOF :: *;
import SpecialFIFOs :: *;
import Clocks :: *;
import GetPut :: *;

typedef enum {
  OKAY = 2'b00,
  // EXOKAY = 2'b01, no lock in AXI4-Lite
  SLVERR = 2'b10,
  DECERR = 2'b11
} AXI4_Lite_Response
deriving(Bits, FShow, Eq);

instance DefaultValue#(AXI4_Lite_Response);
  function defaultValue;
    return OKAY;
  endfunction
endinstance

typedef struct {
  Bit#(addr_bits) addr;
} AXI4_Lite_RRequest#(numeric type addr_bits) deriving(Bits, Eq, FShow);

typedef struct {
  Byte#(data_bytes) bytes;
  AXI4_Lite_Response resp;
} AXI4_Lite_RResponse#(numeric type data_bytes) deriving(Bits, Eq, FShow);

typedef struct {
  Bit#(addr_bits) addr;
  Byte#(data_bytes) bytes;
  Bit#(data_bytes) strb;
} AXI4_Lite_WRequest#(numeric type addr_bits, numeric type data_bytes) deriving(Bits, Eq, FShow);

typedef struct {
  AXI4_Lite_Response resp;
} AXI4_Lite_WResponse deriving(Bits, Eq, FShow);

(* always_ready, always_enabled *)
interface RdAXI4_Lite_Master_Fab#(numeric type addr_bits, numeric type data_bytes);
  (* result= "arvalid" *) method Bool arvalid;
  (* prefix= ""        *) method Action arready((* port= "arready" *) Bool a);
  (* result= "araddr"  *) method Bit#(addr_bits) araddr;

  (* result= "rready" *) method Bool rready;
  (* prefix= ""       *) method Action rvalid((* port="rvalid" *)Bool v);
  (* prefix= ""       *) method Action rdata((* port="rdata" *)Byte#(data_bytes) d);
  (* prefix= ""       *) method Action rresp((* port="rresp" *)AXI4_Lite_Response resp);
endinterface

(* always_ready, always_enabled *)
interface RdAXI4_Lite_Slave_Fab#(numeric type addr_bits, numeric type data_bytes);
  (* result= "arready" *) method Bool arready;
  (* prefix=""         *) method Action arvalid((* port="arvalid" *) Bool arvalid);
  (* prefix=""         *) method Action araddr((* port="araddr" *) Bit#(addr_bits) a);

  (* result= "rvalid" *) method Bool rvalid;
  (* prefix= ""       *) method Action rready((* port="rready" *)Bool rready);
  (* result= "rdata"  *) method Byte#(data_bytes) rdata();
  (* result= "rresp"  *) method AXI4_Lite_Response rresp();
endinterface

instance Connectable#(RdAXI4_Lite_Slave_Fab#(a, d), RdAXI4_Lite_Master_Fab#(a, d));
  module mkConnection#(RdAXI4_Lite_Slave_Fab#(a, d) slave, RdAXI4_Lite_Master_Fab#(a, d) master)(Empty);
    rule arvalid; slave.arvalid(master.arvalid); endrule
    rule arready; master.arready(slave.arready); endrule
    rule araddr; slave.araddr(master.araddr); endrule

    rule rready; slave.rready(master.rready); endrule
    rule rvalid; master.rvalid(slave.rvalid); endrule
    rule rdata; master.rdata(slave.rdata); endrule
    rule rresp; master.rresp(slave.rresp); endrule
  endmodule
endinstance

instance Connectable#(RdAXI4_Lite_Master_Fab#(a, d), RdAXI4_Lite_Slave_Fab#(a, d));
  module mkConnection#(RdAXI4_Lite_Master_Fab#(a, d) master, RdAXI4_Lite_Slave_Fab#(a, d) slave)(Empty);
    mkConnection(slave, master);
  endmodule
endinstance

interface RdAXI4_Lite_Master#(numeric type addr_bits, numeric type data_bytes);
  interface Get#(AXI4_Lite_RRequest#(addr_bits)) request;
  interface Put#(AXI4_Lite_RResponse#(data_bytes)) response;
endinterface

interface RdAXI4_Lite_Slave#(numeric type addr_bits, numeric type data_bytes);
  interface Put#(AXI4_Lite_RRequest#(addr_bits)) request;
  interface Get#(AXI4_Lite_RResponse#(data_bytes)) response;
endinterface

instance Connectable#(RdAXI4_Lite_Slave#(a, d), RdAXI4_Lite_Master#(a, d));
  module mkConnection#(RdAXI4_Lite_Slave#(a, d) slave, RdAXI4_Lite_Master#(a, d) master)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.request, master.request);
  endmodule
endinstance

instance Connectable#(RdAXI4_Lite_Master#(a, d), RdAXI4_Lite_Slave#(a, d));
  module mkConnection#(RdAXI4_Lite_Master#(a, d) master, RdAXI4_Lite_Slave#(a, d) slave)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.request, master.request);
  endmodule
endinstance

(* always_ready, always_enabled *)
interface WrAXI4_Lite_Master_Fab#(numeric type addr_bits, numeric type data_bytes);
  (* prefix= ""        *) method Action awready((* port="awready" *) Bool r);
  (* result= "awvalid" *) method Bool awvalid;
  (* result= "awaddr"  *) method Bit#(addr_bits) awaddr;

  (* prefix= ""       *) method Action wready((* port="wready" *)Bool r);
  (* prefix= "wvalid" *) method Bool wvalid;
  (* prefix= "wdata"  *) method Byte#(data_bytes) wdata;
  (* prefix= "wstrb"  *) method Bit#(data_bytes) wstrb;

  (* prefix= ""       *) method Action bvalid((* port="bvalid" *) Bool b);
  (* result= "bready" *) method Bool bready;
  (* prefix= ""       *) method Action bresp((* port="bresp" *) AXI4_Lite_Response r);
endinterface

(* always_ready, always_enabled *)
interface WrAXI4_Lite_Slave_Fab#(numeric type addr_bits, numeric type data_bytes);
  (* result= "awready" *) method Bool awready;
  (* prefix=""         *) method Action awvalid((* port="awvalid" *) Bool awvalid);
  (* prefix=""         *) method Action awaddr((* port="awaddr" *) Bit#(addr_bits) a);

  (* result= "wready" *) method Bool wready;
  (* prefix=""        *) method Action wvalid((* port="wvalid" *) Bool wvalid);
  (* prefix=""        *) method Action wdata((* port="wdata" *) Byte#(data_bytes) a);
  (* prefix=""        *) method Action wstrb((* port="wstrb" *) Bit#(data_bytes) p);

  (* result= "bvalid" *) method Bool bvalid;
  (* prefix=""        *) method Action bready((* port="bready" *) Bool b);
  (* result= "bresp"  *) method AXI4_Lite_Response bresp();
endinterface

instance Connectable#(WrAXI4_Lite_Slave_Fab#(a, d), WrAXI4_Lite_Master_Fab#(a, d));
  module mkConnection#(WrAXI4_Lite_Slave_Fab#(a, d) slave, WrAXI4_Lite_Master_Fab#(a, d) master)(Empty);
    rule awready; master.awready(slave.awready); endrule
    rule awvalid; slave.awvalid(master.awvalid); endrule
    rule awaddr; slave.awaddr(master.awaddr); endrule

    rule wready; master.wready(slave.wready); endrule
    rule wvalid; slave.wvalid(master.wvalid); endrule
    rule wdata; slave.wdata(master.wdata); endrule
    rule wstrb; slave.wstrb(master.wstrb); endrule

    rule bvalid; master.bvalid(slave.bvalid); endrule
    rule bready; slave.bready(master.bready); endrule
    rule bresp; master.bresp(slave.bresp); endrule
  endmodule
endinstance

instance Connectable#(WrAXI4_Lite_Master_Fab#(a, d), WrAXI4_Lite_Slave_Fab#(a, d));
  module mkConnection#(WrAXI4_Lite_Master_Fab#(a, d) master, WrAXI4_Lite_Slave_Fab#(a, d) slave)(Empty);
    mkConnection(slave, master);
  endmodule
endinstance

interface WrAXI4_Lite_Master#(numeric type addr_bits, numeric type data_bytes);
  interface Get#(AXI4_Lite_WRequest#(addr_bits, data_bytes)) request;
  interface Put#(AXI4_Lite_WResponse) response;
endinterface

interface WrAXI4_Lite_Slave#(numeric type addr_bits, numeric type data_bytes);
  interface Put#(AXI4_Lite_WRequest#(addr_bits, data_bytes)) request;
  interface Get#(AXI4_Lite_WResponse) response;
endinterface

instance Connectable#(WrAXI4_Lite_Slave#(a, d), WrAXI4_Lite_Master#(a, d));
  module mkConnection#(WrAXI4_Lite_Slave#(a, d) slave, WrAXI4_Lite_Master#(a, d) master)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.request, master.request);
  endmodule
endinstance

instance Connectable#(WrAXI4_Lite_Master#(a, d), WrAXI4_Lite_Slave#(a, d));
  module mkConnection#(WrAXI4_Lite_Master#(a, d) master, WrAXI4_Lite_Slave#(a, d) slave)(Empty);
    mkConnection(slave.response, master.response);
    mkConnection(slave.request, master.request);
  endmodule
endinstance

interface RdAXI4_Lite_Master_IFC#(numeric type a, numeric type d);
  (* prefix= "" *) interface RdAXI4_Lite_Master_Fab#(a, d) fabric;
  interface RdAXI4_Lite_Slave#(a, d) server;
endinterface

interface RdAXI4_Lite_Slave_IFC#(numeric type a, numeric type d);
  (* prefix= "" *) interface RdAXI4_Lite_Slave_Fab#(a, d) fabric;
  interface RdAXI4_Lite_Master#(a, d) client;
endinterface

interface WrAXI4_Lite_Master_IFC#(numeric type a, numeric type d);
  (* prefix= "" *) interface WrAXI4_Lite_Master_Fab#(a, d) fabric;
  interface WrAXI4_Lite_Slave#(a, d) server;
endinterface

interface WrAXI4_Lite_Slave_IFC#(numeric type a, numeric type d);
  (* prefix= "" *) interface WrAXI4_Lite_Slave_Fab#(a, d) fabric;
  interface WrAXI4_Lite_Master#(a, d) client;
endinterface

// conversion between read master `fabric` and `fifof` interfaces
module mkRdAXI4_Lite_Master#(Integer buffSize) (RdAXI4_Lite_Master_IFC#(addr_bits, data_bytes));
  FIFOF#(AXI4_Lite_RRequest#(addr_bits)) request <- mkSizedBypassFIFOF(buffSize);
  FIFOF#(AXI4_Lite_RResponse#(data_bytes)) response <- mkSizedBypassFIFOF(buffSize);

  let isRst <- isResetAsserted();

  Wire#(Bool) wire_arvalid <- mkBypassWire();
  Wire#(Bool) wire_arready <- mkBypassWire();
  Wire#(Bit#(addr_bits)) wire_araddr <- mkBypassWire();

  Wire#(Bool) wire_rvalid <- mkBypassWire();
  Wire#(Bool) wire_rready <- mkBypassWire();
  Wire#(Byte#(data_bytes)) wire_rdata <- mkBypassWire();
  Wire#(AXI4_Lite_Response) wire_rresp <- mkBypassWire();

  rule step;
    if (request.notEmpty() && !isRst) begin
      wire_arvalid <= True;
      wire_araddr <= request.first().addr;
      if (wire_arready) request.deq();
    end else begin
      wire_arvalid <= False;
      wire_araddr <= 0;
    end

    if (response.notFull() && !isRst) begin
      wire_rready <= True;
      if (wire_rvalid)
        response.enq(AXI4_Lite_RResponse{bytes: wire_rdata, resp: wire_rresp});
    end else begin
      wire_rready <= False;
    end
  endrule

  interface RdAXI4_Lite_Slave server;
    interface request = toPut(request);
    interface response = toGet(response);
  endinterface

  interface RdAXI4_Lite_Master_Fab fabric;
    interface arready = wire_arready._write;
    interface arvalid = wire_arvalid;
    interface araddr = wire_araddr;

    interface rready = wire_rready;
    interface rvalid = wire_rvalid._write;
    interface rdata = wire_rdata._write;
    interface rresp = wire_rresp._write;
  endinterface
endmodule

// conversion between read slave `fabric` and `fifof` interfaces
module mkRdAXI4_Lite_Slave#(Integer buffSize) (RdAXI4_Lite_Slave_IFC#(addr_bits, data_bytes));
  FIFOF#(AXI4_Lite_RRequest#(addr_bits)) request <- mkSizedBypassFIFOF(buffSize);
  FIFOF#(AXI4_Lite_RResponse#(data_bytes)) response <- mkSizedBypassFIFOF(buffSize);

  let isRst <- isResetAsserted();

  Wire#(Bool) wire_arvalid <- mkBypassWire();
  Wire#(Bool) wire_arready <- mkBypassWire();
  Wire#(Bit#(addr_bits)) wire_araddr <- mkBypassWire();

  Wire#(Bool) wire_rvalid <- mkBypassWire();
  Wire#(Bool) wire_rready <- mkBypassWire();
  Wire#(Byte#(data_bytes)) wire_rdata <- mkBypassWire();
  Wire#(AXI4_Lite_Response) wire_rresp <- mkBypassWire();

  rule step;
    if (request.notFull() && !isRst) begin
      wire_arready <= True;
      if (wire_arvalid)
        request.enq(AXI4_Lite_RRequest{addr:wire_araddr});
    end else begin
      wire_arready <= False;
    end

    if (response.notEmpty() && !isRst) begin
      wire_rvalid <= True;
      wire_rdata <= response.first().bytes;
      wire_rresp <= response.first().resp;
      if (wire_rvalid) response.deq();
    end else begin
      wire_rready <= False;
      wire_rdata <= 0;
      wire_rresp <= OKAY;
    end
  endrule

  interface RdAXI4_Lite_Master client;
    interface request = toGet(request);
    interface response = toPut(response);
  endinterface

  interface RdAXI4_Lite_Slave_Fab fabric;
    interface arready = wire_arready;
    interface arvalid = wire_arvalid._write;
    interface araddr = wire_araddr._write;

    interface rready = wire_rready._write;
    interface rvalid = wire_rvalid;
    interface rdata = wire_rdata;
    interface rresp = wire_rresp;
  endinterface
endmodule



// conversion between read master `fabric` and `fifof` interfaces
module mkWrAXI4_Lite_Master#(Integer buffSize) (WrAXI4_Lite_Master_IFC#(addr_bits, data_bytes));
  FIFOF#(AXI4_Lite_WRequest#(addr_bits, data_bytes)) request <- mkSizedBypassFIFOF(buffSize);

  FIFOF#(Bit#(addr_bits)) addr_fifo <- mkBypassFIFOF();
  FIFOF#(Tuple2#(Byte#(data_bytes), Bit#(data_bytes))) data_fifo <- mkBypassFIFOF();

  FIFOF#(AXI4_Lite_WResponse) response <- mkSizedBypassFIFOF(buffSize);

  let isRst <- isResetAsserted();

  Wire#(Bool) wire_awready <- mkBypassWire;
  Wire#(Bool) wire_awvalid <- mkBypassWire;
  Wire#(Bit#(addr_bits)) wire_awaddr <- mkBypassWire;

  Wire#(Bool) wire_wready <- mkBypassWire;
  Wire#(Bool) wire_wvalid <- mkBypassWire;
  Wire#(Byte#(data_bytes)) wire_wdata <- mkBypassWire;
  Wire#(Bit#(data_bytes)) wire_wstrb <- mkBypassWire;

  Wire#(Bool) wire_bready <- mkBypassWire;
  Wire#(Bool) wire_bvalid <- mkBypassWire;
  Wire#(AXI4_Lite_Response) wire_bresp <- mkBypassWire;


  rule request_fifo_deq;
    addr_fifo.enq(request.first().addr);
    data_fifo.enq(Tuple2{fst: request.first().bytes, snd: request.first().strb});
    request.deq();
  endrule

  rule step;
    // send address
    if (!isRst && addr_fifo.notEmpty()) begin
      wire_awvalid <= True;
      wire_awaddr <= addr_fifo.first();
      if (wire_awready) addr_fifo.deq();
    end else begin
      wire_awvalid <= False;
      wire_awaddr <= 0;
    end

    // send data
    if (!isRst && data_fifo.notEmpty()) begin
      wire_wvalid <= True;
      wire_wdata <= data_fifo.first().fst;
      wire_wstrb <= data_fifo.first().snd;
      if (wire_wready) data_fifo.deq();
    end else begin
      wire_wvalid <= False;
      wire_wdata <= 0;
      wire_wstrb <= 0;
    end

    // receive response
    if (!isRst && response.notFull()) begin
      wire_bready <= True;
      if (wire_bvalid)
        response.enq(AXI4_Lite_WResponse{resp: wire_bresp});
    end else begin
      wire_bready <= False;
    end
  endrule

  interface WrAXI4_Lite_Slave server;
    interface request = toPut(request);
    interface response = toGet(response);
  endinterface

  interface WrAXI4_Lite_Master_Fab fabric;
    interface awready = wire_awready._write;
    interface awvalid = wire_awvalid;
    interface awaddr = wire_awaddr;

    interface wready = wire_wready._write;
    interface wvalid = wire_wvalid;
    interface wdata = wire_wdata;
    interface wstrb = wire_wstrb;

    interface bready = wire_bready;
    interface bvalid = wire_bvalid._write;
    interface bresp = wire_bresp._write;
  endinterface
endmodule

// conversion between read master `fabric` and `fifof` interfaces
module mkWrAXI4_Lite_Slave#(Integer buffSize) (WrAXI4_Lite_Slave_IFC#(addr_bits, data_bytes));
  FIFOF#(AXI4_Lite_WRequest#(addr_bits, data_bytes)) request <- mkSizedBypassFIFOF(buffSize);

  FIFOF#(Bit#(addr_bits)) addr_fifo <- mkBypassFIFOF();
  FIFOF#(Tuple2#(Byte#(data_bytes), Bit#(data_bytes))) data_fifo <- mkBypassFIFOF();

  FIFOF#(AXI4_Lite_WResponse) response <- mkSizedBypassFIFOF(buffSize);

  let isRst <- isResetAsserted();

  Wire#(Bool) wire_awready <- mkBypassWire;
  Wire#(Bool) wire_awvalid <- mkBypassWire;
  Wire#(Bit#(addr_bits)) wire_awaddr <- mkBypassWire;

  Wire#(Bool) wire_wready <- mkBypassWire;
  Wire#(Bool) wire_wvalid <- mkBypassWire;
  Wire#(Byte#(data_bytes)) wire_wdata <- mkBypassWire;
  Wire#(Bit#(data_bytes)) wire_wstrb <- mkBypassWire;

  Wire#(Bool) wire_bready <- mkBypassWire;
  Wire#(Bool) wire_bvalid <- mkBypassWire;
  Wire#(AXI4_Lite_Response) wire_bresp <- mkBypassWire;


  rule request_fifo_enq;
    request.enq(AXI4_Lite_WRequest{
      addr: addr_fifo.first(),
      bytes: data_fifo.first().fst,
      strb: data_fifo.first().snd
    });
    addr_fifo.deq();
    data_fifo.deq();
  endrule

  rule step;
    // receive address
    if (!isRst && addr_fifo.notFull()) begin
      wire_awready <= True;
      if (wire_awvalid)
        addr_fifo.enq(wire_awaddr);
    end else begin
      wire_awready <= False;
    end

    // receive data
    if (!isRst && data_fifo.notEmpty()) begin
      wire_wready <= True;
      if (wire_wvalid)
        data_fifo.enq(Tuple2{fst: wire_wdata, snd: wire_wstrb});
    end else begin
      wire_wready <= False;
    end

    // send response
    if (!isRst && response.notEmpty()) begin
      wire_bvalid <= True;
      wire_bresp <= response.first().resp;
      if (wire_bready) response.deq();
    end else begin
      wire_bvalid <= False;
      wire_bresp <= OKAY;
    end
  endrule

  interface WrAXI4_Lite_Master client;
    interface request = toGet(request);
    interface response = toPut(response);
  endinterface

  interface WrAXI4_Lite_Slave_Fab fabric;
    interface awready = wire_awready;
    interface awvalid = wire_awvalid._write;
    interface awaddr = wire_awaddr._write;

    interface wready = wire_wready;
    interface wvalid = wire_wvalid._write;
    interface wdata = wire_wdata._write;
    interface wstrb = wire_wstrb._write;

    interface bready = wire_bready._write;
    interface bvalid = wire_bvalid;
    interface bresp = wire_bresp;
  endinterface
endmodule

endpackage
