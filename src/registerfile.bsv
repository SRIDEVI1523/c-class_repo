//See LICENSE.iitm for license details
/*

Author : Neel Gala
Email id : neelgala@gmail.com
Details:
This module implements the integer and floating point register files. They are currently implemented
as RegFile. The integer register file requires 2 read and 1 write ports.
The floating point registerfile however will require 3 read ports and 1 write ports

On system reset,  the register files are initialized to 0. This phase will take 32 cycles total.
Only after the initialization phase can the

the debug interface allows the debugger to read / write from / to either of the registerfiles.
This interface should be made mutually exclusive with respect to the other rules accessing the
register files,  otherwise they will require dedicated extra ports. This scheduling is done
implicitly by bluespec owing to the sequence in which the methods have been written,  The debugger
however cannot read the values in the initialization phase.

--------------------------------------------------------------------------------------------------
*/
package registerfile;
	/*==== Project Imports === */
	import ccore_types::*;
	`include "ccore_params.defines"
	/*======================== */
	/*===== Package Imports ==== */
	import RegFile::*;
	import ConfigReg::*;
  import GetPut::*;
  `include "Logger.bsv"
	/*===========================*/

	interface Ifc_registerfile;
    method ActionValue#(Bit#(ELEN)) read_rs1(Bit#(5) addr `ifdef spfpu, RFType rs1type `endif );
    method ActionValue#(Bit#(ELEN)) read_rs2(Bit#(5) addr `ifdef spfpu, RFType rs2type `endif );
  `ifdef spfpu
    method ActionValue#(Bit#(FLEN)) read_rs3(Bit#(5) addr);
  `endif
		method Action commit_rd (CommitData c);
	endinterface

	(*synthesize*)
	module mkregisterfile#(parameter Bit#(XLEN) hartid) (Ifc_registerfile);
    String rf ="";
		RegFile#(Bit#(5), Bit#(XLEN)) integer_rf <- mkRegFileWCF(0, 31);
	`ifdef spfpu
		RegFile#(Bit#(5), Bit#(FLEN)) floating_rf <- mkRegFileWCF(0, 31);
	`endif
		Reg#(Bool) initialize <- mkReg(True);
		Reg#(Bit#(5)) rg_index <- mkReg(0);

    // The following rule is fired on system reset and writes all the register values to "0". This
    // rule will never fire otherwise
		rule initialize_regfile(initialize);
		`ifdef spfpu
		  floating_rf.upd(rg_index, 0);
		`endif
			integer_rf.upd(rg_index, 0);
			rg_index <= rg_index + 1;
			if(rg_index == 'd31)
				initialize <= False;
        `logLevel( rf, 1, $format("[%2d]RF : Initialization phase. Count: %d",hartid,rg_index))
		endrule


    // This method will read operand1 using rs1addr from the decode stage. If there a commit in the
    // same cycle to rs1addr, then that value if bypassed else the value is read from the
    // corresponding register file.
    // Explicit Conditions : fire only when initialize is False;
    // Implicit Conditions : None
    method ActionValue#(Bit#(ELEN)) read_rs1(Bit#(5) addr `ifdef spfpu, RFType rs1type `endif )
                                                                                    if(!initialize);
    `ifdef spfpu
      if(rs1type == FRF)
        return zeroExtend(floating_rf.sub(addr));
      else
    `endif
        return zeroExtend(integer_rf.sub(addr)); // zero extend is required when XLEN<ELEN
    endmethod
    // This method will read operand2 using rs2addr from the decode stage. If there a commit in the
    // same cycle to rs2addr, then that value if bypassed else the value is read from the
    // corresponding register file.
    // Explicit Conditions : fire only when initialize is False;
    // Implicit Conditions : None
    method ActionValue#(Bit#(ELEN)) read_rs2(Bit#(5) addr `ifdef spfpu, RFType rs2type `endif )
                                                                                    if(!initialize);
    `ifdef spfpu
      if(rs2type == FRF)
        return zeroExtend(floating_rf.sub(addr));
      else
    `endif
        return zeroExtend(integer_rf.sub(addr));// zero extend is required when XLEN<ELEN
    endmethod
  `ifdef spfpu
    // This method will read operand3 using rs3addr from the decode stage. If there a commit in the
    // same cycle to rs2addr, then that value if bypassed else the value is read from the
    // Floating register file. Integer RF is not looked - up for rs3 at all.
    // Explicit Conditions : fire only when initialize is False;
    // Implicit Conditions : None
    method ActionValue#(Bit#(FLEN)) read_rs3(Bit#(5) addr) if(!initialize);
      return floating_rf.sub(addr);
    endmethod
  `endif

    // This method is fired when the write - back stage performs a commit and needs to update the RF.
    // The value being commited is updated in the respective register file and also bypassed to the
    // above methods for operand forwarding.
    // Explicit Conditions : fire only when initialize is False;
    // Implicit Conditions : None
		method Action commit_rd (CommitData c) if(!initialize);
      `logLevel( rf, 1, $format("[%2d]RF : Writing Rd: %d(%h) ",hartid,c.addr, c.data
                                                  `ifdef spfpu, fshow(c.rdtype) `endif ))

      `ifdef spfpu
        if(c.rdtype == FRF)begin
			  	floating_rf.upd(c.addr, truncate(c.data));
        end else
      `endif
			  if(c.addr != 0)begin
			  	integer_rf.upd(c.addr, truncate(c.data)); // truncate is required when XLEN<ELEN
			  end
		endmethod
	endmodule
endpackage
