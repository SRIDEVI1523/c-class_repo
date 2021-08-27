//See LICENSE.iitm for license details
/*
Author: Neel Gala
Email id: neelgala@gmail.com
Details:

--------------------------------------------------------------------------------------------------
*/
package TbSoc;
  import Soc:: *;
  import Clocks::*;
  import GetPut:: *;
	import Semi_FIFOF:: *;
	import AXI4_Types:: *;
	import AXI4_Fabric:: *;
  import uart::*;
	import ccore_types::*;
	import csrbox_decoder :: * ;
  import csrbox :: * ;
  `include "ccore_params.defines"
  `include "Logger.bsv"
  `include "Soc.defines"
  `include "csrbox.defines"
  import device_common::*;
  import DReg :: *;
  import Connectable :: *;
`ifdef debug
  import DebugSoc     :: * ;
`endif

`ifdef openocd
  import "BDPI" function ActionValue #(int) init_rbb_jtag(Bit#(1) dummy);
  import "BDPI" function ActionValue #(Bit #(8))get_frame(int client_fd);
  import "BDPI" function Action send_tdo(Bit #(1) tdo , int client_fd);
`endif
    function Bit#(XLEN) fn_atomic_op (Bit#(5) op,  Bit#(XLEN) rs2,  Bit#(XLEN) loaded);
      Bit#(XLEN) op1 = loaded;
      Bit#(XLEN) op2 = rs2;
    `ifdef RV64
      if(op[4]==0)begin
	  		op1=signExtend(loaded[31:0]);
        op2= signExtend(rs2[31:0]);
      end
    `endif
      Int#(XLEN) s_op1 = unpack(op1);
	  	Int#(XLEN) s_op2 = unpack(op2);

      case (op[3:0])
	  			'b0011:return op2;
	  			'b0000:return (op1+op2);
	  			'b0010:return (op1^op2);
	  			'b0110:return (op1&op2);
	  			'b0100:return (op1|op2);
	  			'b1100:return min(op1,op2);
	  			'b1110:return max(op1,op2);
	  			'b1000:return pack(min(s_op1,s_op2));
	  			'b1010:return pack(max(s_op1,s_op2));
	  			default:return op1;
	  		endcase
    endfunction
  (*synthesize*)
  module mkTbSoc(Empty);

    let def_clk <- exposeCurrentClock;
    let def_rst <- exposeCurrentReset;

    MakeClockIfc#(Bit#(1)) tck_clk <-mkUngatedClock(1);
    MakeResetIfc trst <- mkReset(0,False,tck_clk.new_clk);

  `ifdef debug
    Ifc_DebugSoc soc <- mkDebugSoc(tck_clk.new_clk,trst.new_rst);
  `else
    Ifc_Soc soc <- mkSoc();
  `endif
  
  `ifdef rtldump
    `include "csr_probe.bsv"
  `endif

    UserInterface#(`paddr,XLEN,16) uart <- mkuart_user(5);
    Reg#(Bool) rg_read_rx<- mkDReg(False);

    Reg#(Bit#(5)) rg_cnt <-mkReg(0);

    rule display_eol;
	    let timeval <- $time;
      `logLevel( tb, 0, $format("\n[%10d]", timeval))
    endrule

  `ifdef rtldump
 	  let dump <- mkReg(InvalidFile) ;
    rule open_file_rtldump(rg_cnt<5);
      let generate_dump <- $test$plusargs("rtldump");
      if(generate_dump) begin
        String dumpFile = "rtl.dump" ;
    	  File lfh <- $fopen( dumpFile, "w" ) ;
    	  if ( lfh == InvalidFile )begin
    	    `logLevel( tb, 0, $format("TB: cannot open %s", dumpFile))
    	    $finish(0);
    	  end
    	  dump <= lfh ;
      end
    endrule
  `endif

 	  let dump1 <- mkReg(InvalidFile) ;
    rule open_file_app(rg_cnt<5);
      String dumpFile1 = "app_log" ;
    	File lfh1 <- $fopen( dumpFile1, "w" ) ;
    	if (lfh1==InvalidFile )begin
    	  `logLevel( tb, 0, $format("TB: cannot open %s", dumpFile1))
    	  $finish(0);
    	end
      dump1 <= lfh1;
    	rg_cnt <= rg_cnt+1 ;
    endrule

    rule connect_uart_out;
      soc.uart_io.sin(uart.io.sout);
    endrule
    rule connect_uart_in;
      uart.io.sin(soc.uart_io.sout);
    endrule

    rule check_if_character_present(!rg_read_rx);
      let {data,err}<- uart.read_req('hc,Byte);
      if (data[3]==1) // character present
        rg_read_rx<=True;
    endrule

    rule write_received_character(rg_cnt>=5 && rg_read_rx);
      let {data,err}<-uart.read_req('h8,Byte);
      $fwrite(dump1,"%c",data);
    endrule

  `ifdef rtldump

    rule write_dump_file(rg_cnt >= 5);

      let generate_dump <- $test$plusargs("rtldump");
      if (soc.commitlog matches tagged Valid .idump) begin
    `ifndef openocd `ifndef cocotb_sim
      if(idump.instruction=='h00006f||idump.instruction =='h00a001)
        $finish(0);
      else
    `endif `endif
      if(generate_dump) begin
        if (idump.instruction[1:0] == 'b11)
        	$fwrite(dump, "core   0: ", idump.mode, " 0x%16h", idump.pc, " (0x%8h", idump.instruction, ")");
        else
          $fwrite(dump, "core   0: ", idump.mode, " 0x%16h", idump.pc, " (0x%4h", idump.instruction[15:0], ")");

        if (idump.inst_type matches tagged REG .d) begin
          if (!(idump.instruction[31:25] =='b0001001 && idump.instruction[14:0] == 'b000000001110011)) begin
            if (d.irf && valueOf(XLEN) == 64 && d.rd != 0)
              $fwrite(dump, " x%d", d.rd, " 0x%16h", d.wdata);
            if (d.irf && valueOf(XLEN) == 32 && d.rd != 0)
              $fwrite(dump, " x%d", d.rd, " 0x%8h", d.wdata);
            if (!d.irf && valueOf(FLEN) == 64)
              $fwrite(dump, " f%d", d.rd, " 0x%16h", d.wdata);
            if (!d.irf && valueOf(FLEN) == 32)
              $fwrite(dump, " f%d", d.rd, " 0x%8h", d.wdata);
          end
        end

        if (idump.inst_type matches tagged CSR .d) begin
          let csr_address = d.csr_address;
          if (d.csr_address == 'h100)
            csr_address = 'h300;
          if (valueOf(XLEN) == 64 && d.rd != 0)
            $fwrite(dump, " x%d", d.rd, " 0x%16h", d.rdata);
          if (valueOf(XLEN) == 32 && d.rd != 0)
            $fwrite(dump, " x%d", d.rd, " 0x%8h", d.rdata);
          Bit#(XLEN) wdata = fn_probe_csr(csr_address);
          if (!(d.op==2'b10 && idump.instruction[19:15] == 0)) begin
            if (valueOf(XLEN) == 64) 
              $fwrite(dump, " " , fn_csr_to_str(csr_address), " 0x%16h", wdata);
            if (valueOf(XLEN) == 32)
              $fwrite(dump, " " , fn_csr_to_str(csr_address), " 0x%8h", wdata);
          end
        end

        if (idump.inst_type matches tagged MEM .d) begin
          let store_data = d.data;
        `ifdef atomic
          if (d.access == Atomic && d.atomic_op != 5 && d.atomic_op != 7) begin
            store_data = fn_atomic_op(d.atomic_op,d.data, d.commit_data);
          end
        `endif
          if (d.access == Load `ifdef atomic || d.access == Atomic `endif ) begin
            if (d.irf && valueOf(XLEN) == 64 && d.rd != 0)
              $fwrite(dump, " x%d", d.rd, " 0x%16h", d.commit_data);
            if (d.irf && valueOf(XLEN) == 32 && d.rd != 0)
              $fwrite(dump, " x%d", d.rd, " 0x%8h", d.commit_data);
            if (!d.irf && valueOf(FLEN) == 64 )
              $fwrite(dump, " f%d", d.rd, " 0x%16h", d.commit_data);
            if (!d.irf && valueOf(FLEN) == 32 )
              $fwrite(dump, " f%d", d.rd, " 0x%8h", d.commit_data);
          end

          if(valueOf(XLEN) ==64 && d.access != Fence && d.access != FenceI)
            $fwrite(dump, " mem 0x%16h", d.address);
          if(valueOf(XLEN) ==32&& d.access != Fence && d.access != FenceI)
            $fwrite(dump, " mem 0x%8h", d.address);

        `ifdef atomic
          if (d.access == Atomic && d.atomic_op != 5 && d.atomic_op != 7) begin
            if(valueOf(XLEN) ==64)
              $fwrite(dump, " mem 0x%16h", d.address);
            if(valueOf(XLEN) ==32)
              $fwrite(dump, " mem 0x%8h", d.address);
          end
        `endif

          if (d.access == Store  `ifdef atomic || (d.access == Atomic && d.atomic_op != 5) `endif ) begin
            if (d.size == 0) begin
              if (store_data[7:4]==0)
                $fwrite(dump, " 0x%1h", store_data[3:0]);
              else
                $fwrite(dump, " 0x%2h", store_data[7:0]);
            end
            if (d.size == 1)
              $fwrite(dump, " 0x%4h", store_data[15:0]);
            if (d.size == 2)
              $fwrite(dump, " 0x%8h", store_data[31:0]);
            if (d.size == 3)
              $fwrite(dump, " 0x%16h", store_data);
          end
        end
          $fwrite(dump, "\n");
      end

      end
    endrule
  `endif

  `ifdef debug
    Wire#(Bit#(1)) wr_tdi <-mkWire();
    Wire#(Bit#(1)) wr_tms <-mkWire();
    rule connect_jtag_io;
      soc.wire_tdi(wr_tdi);
      soc.wire_tms(wr_tms);
    endrule
  `endif
  `ifdef openocd
    Wire#(Bit#(1)) wr_tdo <-mkWire();
    Wire#(Bit#(1)) wr_tck <-mkWire();
    Wire#(Bit#(1)) wr_trst <-mkWire();
    rule rl_wr_tdo;
      wr_tdo <= soc.wire_tdo();
    endrule
    Reg#(Bit#(1)) rg_initial <- mkRegA(0);
    Reg#(Bit#(1)) rg_end_sim <- mkRegA(0);
    Reg#(int) rg_client_fd <- mkRegA(32'hffffffff);
    Reg#(Bit#(5)) delayed_actor <- mkReg(0);
    Reg#(Bit#(5)) delayed_actor2 <- mkReg(0);
    Reg#(Bit#(5)) delayed_actor3 <- mkReg(0);
    Reg#(Bit#(5)) delayed_actor4 <- mkReg(0);
    Reg#(Bit#(5)) delayed_actor5 <- mkReg(0);
    rule rl_initial(rg_initial == 0);
      let x <- init_rbb_jtag(0);
      if(x != 32'hffffffff)begin
        rg_initial <= 1'b1;
        rg_client_fd <= x;
      end
    endrule
    rule rl_get_frame((rg_initial == 1'b1));
      let x <- get_frame(rg_client_fd);
      delayed_actor <= truncate(x);
      delayed_actor2 <= delayed_actor;
      delayed_actor3 <= delayed_actor2;
      delayed_actor4 <= delayed_actor3;
      delayed_actor5 <= delayed_actor4;
      tck_clk.setClockValue(delayed_actor2[2]);
      if(delayed_actor2[4] == 1)
        trst.assertReset();
      if(delayed_actor5[3] == 1 )
        send_tdo(wr_tdo,rg_client_fd);
      wr_tdi <= delayed_actor[0];
      wr_tms <= delayed_actor[1];
      if( x[5] == 1)begin
        $display("OpenOcd Exit");
        $finish();
      end
    endrule
  `endif
  endmodule
endpackage: TbSoc
