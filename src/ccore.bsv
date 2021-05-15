//See LICENSE.iitm for license details
/*

Author : Neel Gala
Email id : neelgala@gmail.com
Details:

--------------------------------------------------------------------------------------------------
*/
package ccore;

//=================== Interface and module for a ccore - master on the AXI4 fabric ============= //
// project related imports
import Semi_FIFOF:: *;
import AXI4_Types:: *;
import AXI4_Fabric:: *;
import riscv:: * ;
import ccore_types:: * ;
import FIFOF::*;
import dcache_types :: *;
import icache_types :: * ;
import Assert ::*;
import imem::*;
import dmem::*;

`ifdef supervisor
  `ifdef RV64
    import ptwalk_rv64::*;
  `else
    import ptwalk_rv32::*;
  `endif
`endif

`include "ccore_params.defines"
`include "Logger.bsv"

`define Mem_master_num 0

// package imports
import Connectable 				:: *;
import GetPut:: *;
import BUtils::*;
import csrbox :: * ;

`ifdef debug
  import debug_types  :: * ;
  import csr_types    :: * ;
`endif

`ifdef supervisor
typedef enum {None, IWalk, DWalk} PTWState deriving(Bits, Eq, FShow);
`endif

interface Ifc_ccore_axi4;
	interface AXI4_Master_IFC#(`paddr, ELEN, USERSPACE) master_d;
	interface AXI4_Master_IFC#(`paddr, ELEN, USERSPACE) master_i;
  method Action sb_clint_msip (Bit#(1) m) ;
  method Action sb_clint_mtip (Bit#(1) m) ;
  method Action sb_clint_mtime(Bit#(64) m);
	method Action sb_plic_meip(Bit#(1) ex_i);
`ifdef supervisor
	method Action sb_plic_seip(Bit#(1) ex_i);
`endif
`ifdef usertraps
	method Action sb_plic_ueip(Bit#(1) ex_i);
`endif
`ifdef rtldump
  interface Sbread sbread;
  method Maybe#(CommitLogPacket) commitlog;
`endif
`ifdef debug
  method Action ma_debug_interrupt(Bit#(1) _int);
  method Bit#(1) mv_core_is_reset;
  method Bit#(1) mv_core_debugenable;
  (*always_enabled*)
  method Action ma_debugger_available (Bit#(1) avail);
`endif
endinterface : Ifc_ccore_axi4

(*synthesize*)

`ifdef supervisor
  (*preempts="dtlb_req_to_ptwalk, itlb_req_to_ptwalk"*)
  (*preempts="core_req_mkConnectionGetPut, ptwalk_req_mkConnectionGetPut"*)
`endif

`ifdef itim
  (*conflict_free="handle_itim_write_resp, handle_nc_write_resp"*)
`endif
(*mutually_exclusive ="rl_handle_io_read_response, rl_handle_io_write_resp"*)
module mkccore_axi4#(Bit#(`vaddr) resetpc, parameter Bit#(XLEN) hartid)(Ifc_ccore_axi4);
  String core = "";
  let vaddr = valueOf(`vaddr);
  let paddr = valueOf(`paddr);
  Ifc_riscv riscv <- mkriscv(resetpc, hartid);
`ifdef supervisor  `ifdef RV64
  Ifc_ptwalk_rv64#(`asidwidth) ptwalk <- mkptwalk_rv64;
`else
  Ifc_ptwalk_rv32#(`asidwidth) ptwalk <- mkptwalk_rv32;
`endif
  Reg#(PTWState) rg_ptw_state <- mkReg(None);
`endif

	AXI4_Master_Xactor_IFC #(`paddr, ELEN, USERSPACE) fetch_xactor <- mkAXI4_Master_Xactor;
	AXI4_Master_Xactor_IFC #(`paddr, ELEN, USERSPACE) memory_xactor <- mkAXI4_Master_Xactor;
`ifdef dcache
  Reg#(Bit#(8)) rg_burst_count <- mkReg(0);
  Reg#(Bit#(TLog#(TMul#(TMul#(`dwords, 8), `dblocks)))) rg_shift_amount <- mkReg(`dwords * 8 );
`endif
  let curr_priv = riscv.mv_curr_priv;
`ifdef pmp
  let lv_pmp_cfg = riscv.mv_pmp_cfg;
  let lv_pmp_adr = riscv.mv_pmp_addr;
`endif

	Ifc_imem imem <- mkimem(truncate(hartid) `ifdef pmp ,lv_pmp_cfg, lv_pmp_adr `endif );
	Ifc_dmem dmem <- mkdmem(truncate(hartid) `ifdef pmp ,lv_pmp_cfg, lv_pmp_adr `endif );

	mkConnection(imem.get_core_resp, riscv.inst_response); // imem integration
	mkConnection(imem.put_core_req , riscv.instr_req);
	mkConnection(dmem.mv_storebuffer_empty, riscv.storebuffer_empty);
	mkConnection(dmem.mv_dmem_available, riscv.cache_is_available);

  let core_req <- mkConnection(dmem.receive_core_req, riscv.memory_request);
	let core_resp <- mkConnection(dmem.send_core_cache_resp, riscv.memory_response); // dmem integration


  /*doc:rule: This rule sends out requests from the I-cache to the fabric*/
  rule rl_handle_imem_line_request;
		let request <- imem.get_read_mem_req.get;
		AXI4_Rd_Addr#(`paddr, 0) imem_request = AXI4_Rd_Addr {araddr : truncate(request.address),
      aruser: ?, arlen : request.burst_len, arsize : request.burst_size, arburst : 'b10,
      arid : zeroExtend(pack(request.io)), arprot:{1'b1, 1'b0, curr_priv[1]} }; // arburst : 00 - FIXED 01 - INCR 10 - WRAP
	  fetch_xactor.i_rd_addr.enq(imem_request);
		`logLevel( core, 1, $format("[%2d]CORE : IMEM Line Requesting ",hartid, fshow(imem_request)))
  endrule:rl_handle_imem_line_request

  /*doc:rule: This rule captures the response from the fetch transactor of the fabric and routes
   * the response back to the imem/icache*/
	rule rl_handle_imem_line_resp;
	  let fab_resp <- pop_o (fetch_xactor.o_rd_data);
		Bool bus_error = !(fab_resp.rresp == AXI4_OKAY);
    imem.put_read_mem_resp.put(ICache_mem_readresp{data   : truncate(fab_resp.rdata),
                                               last   : fab_resp.rlast,
                                               err    : bus_error});
		`logLevel( core, 1, $format("[%2d]CORE : IMEM Line Response ",hartid, fshow(fab_resp)))
	endrule:rl_handle_imem_line_resp
  `ifdef icache
    rule rl_imem_enable;
		  imem.ma_cache_enable(unpack(riscv.mv_cacheenable[0]));
    endrule
	`endif

	`ifdef dtim
	  /*doc:rule: */
	  rule rl_connect_dtim_memorymap_csrs;
	    dmem.ma_dtim_memory_map(truncate(riscv.mv_csr_dtim_base), truncate(riscv.mv_csr_dtim_bound));
	  endrule
	`endif
	`ifdef itim
	  /*doc:rule: */
	  rule rl_connect_itim_memorymap_csrs;
	    imem.ma_itim_memory_map(truncate(riscv.mv_csr_itim_base), truncate(riscv.mv_csr_itim_bound));
	  endrule
	`endif

	/*doc:rule: This rule will initiate an IO read or write as indicated by the WB stage of the
	* pipeline. If a burst write is on-going then this rule is stalled.*/
	rule rl_initiate_io( `ifdef dcache rg_burst_count == 0 `endif );
	  let req <- dmem.send_mem_io_req.get;
    `logLevel( core, 0, $format("CORE: Received io op: ",fshow(req)))
    if(req.size[1:0]== 0)
      req.data = duplicate(req.data[7 : 0]);
    else if(req.size[1:0] == 1)
      req.data = duplicate(req.data[15 : 0]);
    else if(req.size[1:0] == 2)
      req.data = duplicate(req.data[31 : 0]);
    Bit#(TDiv#(ELEN, 8)) write_strobe = req.size[1:0] == 0?'b1 :
                                        req.size[1:0] == 1?'b11 :
                                        req.size[1:0] == 2?'hf : '1;
    Bit#(TAdd#(1, TDiv#(ELEN, 32))) byte_offset = truncate(req.address);
    write_strobe = write_strobe<<byte_offset;
	  if (!req.read_write) begin
		  AXI4_Rd_Addr#(`paddr, 0) dmem_request = AXI4_Rd_Addr {araddr : truncate(req.address), aruser: ?,
        arlen : 0, arsize : zeroExtend(req.size[1:0]), arburst : 'b00, // arburst : 00 - FIXED 01 - INCR 10 - WRAP
        arid : 1 ,arprot:{1'b0, 1'b0, curr_priv[1]} }; 
      memory_xactor.i_rd_addr.enq(dmem_request);
	  end
	  else begin
	    AXI4_Wr_Addr#(`paddr, 0) aw = AXI4_Wr_Addr {awaddr : truncate(req.address), awuser : 0,
        awlen : 0, awsize : zeroExtend(req.size[1 : 0]), awburst : 'b0,
        awid : 1, awprot:{1'b0, 1'b0, curr_priv[1]} }; // arburst : 00 - FIXED 01 - INCR 10 - WRAP

      let w  = AXI4_Wr_Data {wdata : truncate(req.data), wstrb : write_strobe,
                             wlast : True, 
                             wid : 1};
	    memory_xactor.i_wr_addr.enq(aw);
	    memory_xactor.i_wr_data.enq(w);
	  end
	endrule:rl_initiate_io
  /*doc:rule: */
  rule rl_handle_io_read_response(memory_xactor.o_rd_data.first.rid == 1);
    let response <- pop_o(memory_xactor.o_rd_data);
  	let bus_error = !(response.rresp == AXI4_OKAY);
    dmem.receive_mem_io_resp.put(DCache_io_response{data:response.rdata, 
                                              error:bus_error});
    `logLevel( core, 1, $format("[%2d]CORE : IO Read Response ",hartid, fshow(response)))
  endrule:rl_handle_io_read_response
  rule rl_handle_io_write_resp (memory_xactor.o_wr_resp.first.bid == 1);
    let response <- pop_o(memory_xactor.o_wr_resp);
  	let bus_error = !(response.bresp == AXI4_OKAY);
    dmem.receive_mem_io_resp.put(DCache_io_response{data: ?, 
                                              error:bus_error});
    `logLevel( core, 1, $format("[%2d]CORE : IO Write Response ",hartid, fshow(response)))
  endrule:rl_handle_io_write_resp


`ifdef dcache
  Reg#(Maybe#(AXI4_Rd_Addr#(`paddr, 0))) rg_read_line_req <- mkReg(tagged Invalid);
  Reg#(Maybe#(Bit#(`paddr))) wr_write_req <- mkReg(tagged Invalid);
  
  rule rl_map_dmem_enable;
	  dmem.ma_cache_enable(unpack(riscv.mv_cacheenable[1]));
  endrule
  mkConnection(dmem.ma_commit_store, riscv.mv_initiate_store);
  mkConnection(dmem.ma_commit_io, riscv.mv_initiate_ioop);
  mkConnection(dmem.send_core_io_resp, riscv.ma_io_response);



  // Currently it is possible that the cache can generate a write - request followed by a
  // read - request, but the fabric (due to contention) latches the read first to the slave followed
  // by the write - req. This could lead to wrong behavior. To avoid this it is necessary to ensure
  // that if a write - request has been initiated no read - requests should be latched unless the
  // write - response has arrived.
  // The contraint is fullilled using the register wr_write_req which holds the current address of
  // the line being written to the fabric on a eviction
  rule rl_handle_dmem_line_read_request(rg_read_line_req matches tagged Invalid );
    Bool perform_req = True;
  	let req <- dmem.send_mem_rd_req.get;
  	AXI4_Rd_Addr#(`paddr, 0) dmem_request = AXI4_Rd_Addr {araddr : truncate(req.address), aruser: ?,
      arlen : req.burst_len, arsize : req.burst_size, arburst : 'b10, // arburst : 00 - FIXED 01 - INCR 10 - WRAP
      arid : 0 ,arprot:{1'b0, 1'b0, curr_priv[1]} }; 
    if(wr_write_req matches tagged Valid .waddr) begin
      if((waddr>>(`dwords + `dblocks )) == (req.address>>(`dwords + `dblocks ) ))begin
        perform_req = False;
        rg_read_line_req <= tagged Valid dmem_request;
        `logLevel( core, 1, $format("[%2d]CORE: Delaying Request: ",hartid,fshow(req)))
      end
    end
    if(perform_req)  begin
 	    memory_xactor.i_rd_addr.enq(dmem_request);
      `logLevel( core, 1, $format("[%2d]CORE : DMEM Line Requesting ",hartid, fshow(dmem_request)))
    end
  endrule

  rule rl_handle_delayed_read(rg_read_line_req matches tagged Valid .r &&& 
                                  wr_write_req matches tagged Invalid );
	  memory_xactor.i_rd_addr.enq(r);
    `logLevel( core, 1, $format("[%2d]CORE : DMEM Delayed Line Requesting ",hartid, fshow(r)))
    rg_read_line_req <= tagged Invalid;
  endrule

	rule rl_handle_dmem_line_resp(memory_xactor.o_rd_data.first.rid == 0);
    let fab_resp <- pop_o (memory_xactor.o_rd_data);
		let lv_data= fab_resp.rdata;
  	Bool bus_error = !(fab_resp.rresp == AXI4_OKAY);
    dmem.receive_mem_rd_resp.put(DCache_mem_readresp{data:truncate(lv_data),
                                               last:fab_resp.rlast,
                                               err :bus_error});
    `logLevel( core, 1, $format("[%2d]CORE : DMEM Line Response ",hartid, fshow(fab_resp)))
  endrule:rl_handle_dmem_line_resp

  rule rl_handle_dmem_write_request (rg_burst_count == 0);
    let req = dmem.send_mem_wr_req;
	  Bit#(TDiv#(ELEN, 8)) write_strobe = '1;
    if(req.burst_len > 0)
      rg_burst_count <= rg_burst_count + 1;
    else begin
      dmem.deq_mem_wr_req;
    end

	  AXI4_Wr_Addr#(`paddr, 0) aw = AXI4_Wr_Addr {awaddr : truncate(req.address), awuser : 0,
      awlen : req.burst_len, awsize : zeroExtend(req.burst_size[1 : 0]), awburst : 'b01,
      awid : 0, awprot:{1'b0, 1'b0, curr_priv[1]} }; // arburst : 00 - FIXED 01 - INCR 10 - WRAP

	  let w  = AXI4_Wr_Data {wdata : truncate(req.data), wstrb : write_strobe,
                           wlast : req.burst_len == 0, 
                           wid : 0};
    memory_xactor.i_wr_addr.enq(aw);
	  memory_xactor.i_wr_data.enq(w);
    `logLevel( core, 1, $format("[%2d]CORE : DMEM Line Write Addr : Request ",hartid, fshow(aw)))
    if(req.burst_len != 0 )
      wr_write_req <= tagged Valid req.address;
  endrule:rl_handle_dmem_write_request

  rule rl_dmem_burst_write_data(rg_burst_count != 0);
    Bool last = rg_burst_count == fromInteger(`dblocks - 1 );
    let req = dmem.send_mem_wr_req;
    req.data = req.data >> rg_shift_amount;
	  let w  = AXI4_Wr_Data {wdata : truncate(req.data), wstrb : '1, wlast : last,
                           wid : 0};
    Bit#(TAdd#(TAdd#(TLog#(`dwords), 1), 3)) shift = {`dwords, 3'b0};
    if(last) begin
      rg_burst_count <= 0;
      rg_shift_amount <= (`dwords * 8);
      wr_write_req <= tagged Invalid;
      dmem.deq_mem_wr_req;
    end
    else begin
      rg_shift_amount <= rg_shift_amount + (`dwords * 8);
      rg_burst_count <= rg_burst_count + 1;
    end
	  memory_xactor.i_wr_data.enq(w);
    `logLevel( core, 1, $format("[%2d]CORE : DMEM Write Data: %h rg_burst_count: %d last: %b \
_shift_amount:%d",hartid, req.data, rg_burst_count, last, rg_shift_amount))
  endrule:rl_dmem_burst_write_data

  rule handle_dmem_line_write_resp (memory_xactor.o_wr_resp.first.bid == 0);
    let response <- pop_o(memory_xactor.o_wr_resp);
  	let bus_error = !(response.bresp == AXI4_OKAY);
	  dmem.receive_mem_wr_resp.put(bus_error);
    `logLevel( core, 1, $format("[%2d]CORE : DMEM Write Line Response ",hartid, fshow(response)))
  endrule: handle_dmem_line_write_resp

`ifdef itim 
  rule handle_dmem_itim_read_response;
  	let response <- imem.get_mem_read_itim_resp.get;
  	Bool bus_error = response.err;
    dmem.put_nc_read_resp.put(DCache_mem_readresp{data:zeroExtend(response.data),
                                              last:True,
                                              err :bus_error});
    `logLevel( core, 1, $format("[%2d]CORE : DMEM ITIM Response ",hartid, fshow(response)))
  endrule
  rule handle_itim_write_resp;
  	let response <- imem.get_mem_write_itim_resp.get;
  	Bool bus_error = response;
  	riscv.ma_io_response(tagged Valid tuple2(pack(bus_error),?));
    `logLevel( core, 1, $format("[%2d]CORE : ITIM Memory Write Response ",hartid, fshow(response)))
  endrule
`endif
`endif

  mkConnection(imem.ma_curr_priv, curr_priv);
  mkConnection(dmem.ma_curr_priv, curr_priv);
`ifdef supervisor
  mkConnection(imem.ma_satp_from_csr,riscv.mv_csr_satp);
  mkConnection(dmem.ma_satp_from_csr, riscv.mv_csr_satp);
  mkConnection(dmem.ma_mstatus_from_csr, riscv.mv_csr_mstatus);
  mkConnection(ptwalk.ma_satp_from_csr,riscv.mv_csr_satp);
  mkConnection(ptwalk.ma_curr_priv, curr_priv);
  mkConnection(ptwalk.ma_mstatus_from_csr, riscv.mv_csr_mstatus);
  rule itlb_req_to_ptwalk(rg_ptw_state == None);
    let req <- imem.get_request_to_ptw.get();
    ptwalk.from_tlb.put(req);
    rg_ptw_state <= IWalk;
  endrule
  rule ptwalk_resp_to_itlb(rg_ptw_state == IWalk);
    let resp <- ptwalk.to_tlb.get();
    imem.put_response_frm_ptw.put(resp);
    rg_ptw_state <= None;
  endrule
  rule dtlb_req_to_ptwalk(rg_ptw_state == None);
    let req <- dmem.get_req_to_ptw.get();
    ptwalk.from_tlb.put(req);
    rg_ptw_state <= DWalk;
  endrule

  rule ptwalk_resp_to_dtlb(rg_ptw_state == DWalk);
    let resp <- ptwalk.to_tlb.get();
    dmem.put_resp_from_ptw.put(resp);
    rg_ptw_state <= None;
  endrule
  let ptwalk_req <- mkConnection(dmem.receive_core_req, ptwalk.request_to_cache);
  mkConnection(dmem.get_ptw_resp, ptwalk.response_frm_cache);
  mkConnection(dmem.get_hold_req, ptwalk.hold_req);
`endif

`ifdef perfmonitors
  `ifdef icache
    mkConnection(riscv.ma_icache_counters,imem.mv_icache_perf_counters);
  `endif
  `ifdef dcache
    mkConnection(riscv.ma_dcache_counters,dmem.mv_dcache_perf_counters);
  `endif
  `ifdef supervisor
    mkConnection(riscv.ma_itlb_counters,imem.mv_itlb_perf_counters);
    mkConnection(riscv.ma_dtlb_counters,dmem.mv_dtlb_perf_counters);
  `endif
`endif   
  
  method sb_clint_msip = riscv.ma_clint_msip;
  method sb_clint_mtip = riscv.ma_clint_mtip; 
  method sb_clint_mtime = riscv.ma_clint_mtime;
	method sb_plic_meip  = riscv.ma_set_meip;
`ifdef supervisor
	method sb_plic_seip = riscv.ma_set_seip;
`endif
`ifdef usertraps
	method sb_plic_ueip = riscv.ma_set_ueip;
`endif
	interface master_i = fetch_xactor.axi_side;
	interface master_d = memory_xactor.axi_side;
`ifdef rtldump
  interface commitlog = riscv.commitlog;
  interface sbread = riscv.sbread;
`endif
`ifdef debug
  method ma_debug_interrupt= riscv.ma_debug_interrupt;
  method mv_core_is_reset = riscv.mv_core_is_reset;
  method mv_core_debugenable = riscv.mv_core_debugenable;
  method ma_debugger_available = riscv.ma_debugger_available;
`endif
endmodule : mkccore_axi4

endpackage
