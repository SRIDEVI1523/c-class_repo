//See LICENSE.iitm for license details
/*

Author: Snehashri Sivaraman
Email id: snehashrisivaraman@gmail.com
Details:
This module primarily holds the combo functions to decode the instructions and provide
various meta data to fetch operands and execute on them.

The module also contains functions to check if a particular csr access is valid or illegal

Interrupt checks are also performed in this package.

The decoder outputs minimal data required to peform operand fetch and executions in the later stage.

--------------------------------------------------------------------------------------------------
*/
package decoder2;

  // pacakge imports from project
  import ccore_types::*;
  import BUtils::*;
  
  import csr_types :: *;
  import csrbox_decoder :: * ;
  `include "ccore_params.defines"
  `include "decoder.defines"

  (*noinline*)
  function Bool hasCSRPermission(Bit#(12) address, Bool write,  Privilege_mode prv);
    Bit#(12) csr_index = pack(address);
    return ((pack(prv) >= csr_index[9:8]) && !(write && csr_index[11:10]==2'b11) );
  endfunction

  // if the operand is not 0 then the instruction will perform a write on the CSR.
  (*noinline*)
	function Bool valid_csr_access(Bit#(12) csr_addr, Bit#(5) operand, Bit#(2) operation,
                                  Bit#(1) tvm, Privilege_mode prv);
		Bool ret = hasCSRPermission(unpack(csr_addr), (operand != 0 || operation=='b01) ? True:False, prv);

    // accessing satp in supervisor mode with tvm=1 should raise an illegal exception
  `ifdef supervisor
    if ( ret && csr_addr == 'h180 && tvm == 1 && prv == Supervisor)
      ret = False;
  `endif
		return ret;
	endfunction

  (*noinline*)
	function Tuple2#(Bit#(`causesize), Bool) chk_interrupt(
	                                                        Privilege_mode prv, 
	                                                        Bit#(XLEN) mstatus,
                                                          Bit#(19) mip, 
                                                          Bit#(19) mie 
                                                        `ifdef non_m_traps 
                                                          ,Bit#(12) mideleg 
                                                        `endif
                                                        `ifdef supervisor `ifdef usertraps
                                                          ,Bit#(12) sideleg 
                                                        `endif `endif
                                                        `ifdef debug
                                                          ,DebugStatus debug, Bool step_done
                                                        `endif );



    Bool m_enabled = (prv != Machine) || (mstatus[3]==1);
  `ifdef supervisor
    Bool s_enabled = (prv == User) || (mstatus[1]==1 && prv==Supervisor);
  `endif
  `ifdef usertraps
    Bool u_enabled = (mstatus[0]==1 && prv==User);
  `endif
    
    Bit#(19) d_interrupts = 0;
    Bit#(19) m_interrupts = 0;
    Bit#(19) s_interrupts = 0;
    Bit#(19) u_interrupts = 0;


  `ifdef debug
    Bool d_enabled = debug.debugger_available && debug.core_debugenable;
    d_interrupts = { mip[18],mip[17],17'd0} & signExtend(pack(d_enabled));
  `endif

    // truncating because in debug mode mie and mip are 14 bits. 12-halt-req 13-resume-req
    m_interrupts =                mie & mip & signExtend(pack(m_enabled))
             `ifdef non_m_traps & ~zeroExtend(mideleg) `endif
             `ifdef debug       & signExtend(pack(!debug.core_is_halted)) `endif ;
  `ifdef supervisor
    s_interrupts =              mie & mip & zeroExtend(mideleg) & signExtend(pack(s_enabled))
               `ifdef usertraps & ~zeroExtend(sideleg) `endif
               `ifdef debug     & signExtend(pack(!debug.core_is_halted)) `endif ;
  `endif
  `ifdef usertraps
    u_interrupts =                mie & mip & zeroExtend(mideleg) & signExtend(pack(u_enabled))
              `ifdef supervisor & sideleg `endif
              `ifdef debug      & signExtend(pack(!debug.core_is_halted)) `endif ;
  `endif

    Bit#(19) pending_interrupts = d_interrupts | m_interrupts | s_interrupts | u_interrupts;
		// format pendingInterrupt value to return
    Bool taketrap=unpack(|pending_interrupts) `ifdef debug ||  (step_done && !debug.core_is_halted) `endif ;

    Bit#(TSub#(`causesize, 1)) int_cause='1;
  `ifdef debug
    if(step_done && !debug.core_is_halted) begin
      int_cause = `HaltStep;
    end
    else if(pending_interrupts[17] == 1)
      int_cause = `HaltDebugger;
    else if(pending_interrupts[18] == 1)
      int_cause = `Resume_int;
    else
  `endif
    if(pending_interrupts[11]==1)
      int_cause=`Machine_external_int;
    else if(pending_interrupts[3]==1)
      int_cause=`Machine_soft_int;
    else if(pending_interrupts[7]==1)
      int_cause=`Machine_timer_int;
  `ifdef perfmonitors
    else if(pending_interrupts[16] == 1)
      int_cause = `CounterInterrupt;
  `endif
  `ifdef supervisor
    else if(pending_interrupts[9]==1)
      int_cause=`Supervisor_external_int;
    else if(pending_interrupts[1]==1)
      int_cause=`Supervisor_soft_int;
    else if(pending_interrupts[5]==1)
      int_cause=`Supervisor_timer_int;
  `endif
  `ifdef user
    else if(pending_interrupts[8]==1)
      int_cause=`User_external_int;
    else if(pending_interrupts[0]==1)
      int_cause=`User_soft_int;
    else if(pending_interrupts[4]==1)
      int_cause=`User_timer_int;
  `endif


		return tuple2({1'b1,int_cause}, taketrap);
	endfunction

  typedef enum {Q0='b00, Q1='b01, Q2='b10} Quadrant deriving(Bits,Eq,FShow);
  (*noinline*)
  function Bit#(5) func_dec_rs1(Bit#(32) inst );
    case (inst) matches
       `JAL_INSTR: return 0 ;
       `LUI_INSTR: return 0 ;
       `AUIPC_INSTR: return 0;
       `ECALL_EBREAK_INSTR: return 0;
        default: return inst[19:15] ;
     endcase
  endfunction
  
  (*noinline*)
  function Op1type func_dec_rs1type(Bit#(32) inst );
    case (inst) matches
       `JAL_INSTR: return PC ;
       `JALR_INSTR: return PC ;
       `AUIPC_INSTR: return PC;
       `ifdef spfpu
       `R4_TYPE: return FloatingRF;
       `FN_INSTR: if (inst[31:28] != 13 || inst[31:28] != 15 ) return FloatingRF; else return IntegerRF;
       `endif
        default: return IntegerRF ;
     endcase
  endfunction
  
  (*noinline*)
  function Bit#(5) func_dec_rs2(Bit#(32) inst, CSRtoDecode csrs );
    case (inst) matches
       `JAL_INSTR: return 0 ;
       `JALR_INSTR: return 0 ;
       `LUI_INSTR: return 0 ;
       `AUIPC_INSTR: return 0;
       `ECALL_EBREAK_INSTR: return 0;
       `ADD_SHIFT_INSTR: return 0;
       `FENCE_INSTR: return 0;
       `LOAD_INSTR: return 0;
       `FLOAD_INSTR: return 0;
       `F_S_INSTR: if ((csrs.csr_misa[3]|csrs.csr_misa[5])==1) return ({3'b000, inst[21:20]}); else return inst[24:20];
       `CSR_INSTR: if (inst[14:12] != 0 && inst[14:12] != 4) return 0; else return inst[24:20];
       `LR_INSTR: return 0;
        default: return inst[24:20] ;
     endcase
  endfunction
  
  (*noinline*)
  function Op2type func_dec_rs2type(Bit#(32) inst `ifdef compressed , Bool compressed `endif );
    case (inst) matches
       `JAL_INSTR: `ifdef compressed if(compressed) return Constant2; else `endif return Constant4;
       `JALR_INSTR: `ifdef compressed if(compressed) return Constant2; else `endif return Constant4;
       `FENCE_INSTR: `ifdef compressed if(compressed) return Constant2; else `endif return Constant4;
       `AUIPC_INSTR: return Immediate;
       `LUI_INSTR: return Immediate;
       `ADD_SHIFT_INSTR: return Immediate;
       `ifdef spfpu
       `R4_TYPE: return FloatingRF;
       `FSTORE_TYPE:  return FloatingRF;
       `FN_INSTR: if (inst[30]==0) return FloatingRF; else return IntegerRF;
       `endif
        default: return IntegerRF ;
     endcase
  endfunction
  
  (*noinline*)
  function Bit#(5) func_dec_rd(Bit#(32) inst );
    case (inst) matches
       `BRANCH_INSTR: return 0 ;
       `STORE_INSTR: return 0 ;
        default: return inst[11:7] ;
     endcase
  endfunction
  
  (*noinline*)
  function Bit#(32) func_dec_immediate(Bit#(32) inst, CSRtoDecode csrs );
    case (inst) matches
       `S_TYPE: return {duplicate(inst[31]), inst[30:25] ,inst[11:8] ,inst[7]} ;
       `FSTORE_TYPE: if (csrs.csr_misa[5]==1) return {duplicate(inst[31]), inst[30:25] ,inst[11:8] ,inst[7]} ; else return 0;
       `B_TYPE: return {duplicate(inst[31]), inst[7], inst[30:25], inst[11:8], 1'b0};
       `U_TYPE: return { inst[31], inst[30:20], inst[19:12], 12'b0};
       `J_TYPE: return { duplicate(inst[31]), inst[19:12], inst[20], inst[30:25], inst[24:21], 1'b0};
  `ifdef atomic
       `A_TYPE: return 32'b0; `endif
       default: return {duplicate(inst[31]), inst[30:25] ,inst[24:21] ,inst[20]} ;
     endcase
  endfunction
  
  (*noinline*)
  function Access_type func_dec_mem_access(Bit#(32) inst);
    case(inst) matches
       `S_TYPE: return Store;
       `FENCE_INSTR: if (inst[12] == 0) return Fence; else return FenceI;
    `ifdef atomic
       `A_TYPE: return Atomic; `endif
    `ifdef supervisor
       `SFENCE_INSTR: return SFence; `endif
       default: return Load;
     endcase
  endfunction
      
 `ifdef spfpu
  (*noinline*)    
  function RFType func_dec_rdtype(Bit#(32) inst );
    case (inst) matches
       `FLOAD_INSTR: return FRF ;
       `FN_INSTR: if(inst[31:28] != 10 || inst[31:28] != 12 || inst[31:28] != 13) return FRF ; else return IRF;
       `R4_TYPE: return FRF;
       default: return IRF ;
     endcase
  endfunction
  
  (*noinline*)
  function Bit#(5) func_dec_rs3(Bit#(32) inst);
    case(inst) matches
       `R4_TYPE: return inst[31:27];
       default: return 0;
     endcase
  endfunction
  
  (*noinline*)
  function RFType func_dec_rs3type(Bit#(32) inst);
    case(inst) matches
       `R4_TYPE: return FRF;
       default: return IRF;
     endcase
  endfunction
  
     `endif
  (*noinline*)
  
  function Instruction_type func_dec_insttype(Bit#(32) inst, Bit#(1) fs, CSRtoDecode csrs, Bool valid_rounding);
    case (inst) matches
       `LOAD_INSTR: `ifdef RV32 if (inst[14:12]!=3 && inst[14:12]!=7) `else if(inst[14:12]!=7) `endif return MEMORY; else return TRAP;
    `ifdef spfpu
       `FLW_INSTR: if (fs!=0 && (csrs.csr_misa[5]==1)) return MEMORY; else return TRAP;
       `ifdef dpfpu
       `FLD_INSTR: if (fs!=0 `ifdef dpfpu && (csrs.csr_misa[3]==1)`endif) return MEMORY; else return TRAP;
       `FSD_INSTR: if (csrs.csr_misa[3]==1 && fs!=0) return MEMORY; else return TRAP;
       `FM_N_ADD_D_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FADD_D_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FQSRT_D_INSTR:  if( valid_rounding && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FSGNJ_D_INSTR: if(inst[13:12] != 3 && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FMIN_MAX_D_INSTR: if( fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FCVT_S_D_INSTR: if( valid_rounding && inst[25]=~inst[20] && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FMV_X_FCLASS_D_INSTR: if( fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FEQ_D_INSTR: if(inst[13:12] != 3 && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FCVT_W_L_D_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FCVT_D_W_L_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `FMV_X_D_INSTR: if( fs!=0 && csrs.csr_misa[3]==1) return FLOAT; else return TRAP;
       `endif
       `FSW_INSTR: if (csrs.csr_misa[5]==1 && fs!=0) return MEMORY; else return TRAP;
       `FM_N_ADD_S_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FADD_S_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FQSRT_S_INSTR:  if( valid_rounding && fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FSGNJ_S_INSTR: if(inst[13:12] != 3 && fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FMIN_MAX_INSTR: if( fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FCVT_W_L_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FMV_X_FCLASS_INSTR: if( fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FEQ_INSTR: if(inst[13:12] != 3 && fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FCVT_S_INSTR: if( valid_rounding && fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
       `FMV_W_INSTR: if( fs!=0 && csrs.csr_misa[5]==1) return FLOAT; else return TRAP;
    `endif
       `AUIPC_INSTR: return ALU;
       `FENCE_INSTR: return MEMORY;
       `SLLI_INSTR: return ALU;
       `SRLI_INSTR: return ALU;
       `SRAI_INSTR: return ALU;
       `ADD_SHIFT_INSTR_32: if (inst[14:12] != 1 || inst[14:12] != 5) return ALU; else return TRAP;
       `ifdef RV64
       `ADDIW_INSTR: return ALU;
       `SLLIW_INSTR:  return ALU;
       `SRLIW_INSTR: return ALU;
       `SRAIW_INSTR: return ALU;
       `endif
     `ifdef RV32
       `STORE_XLEN_INSTR: if (inst[13:12] != 3) return MEMORY; else return TRAP;
      `else
       `STORE_XLEN_INSTR: return MEMORY;
      `endif
  `ifdef atomic
      `LR_W_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `SC_W_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP; 
      `AMOSWAP_W_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOADD_W_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOXOR_W_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOAND_W_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOOR_W_INSTR:   if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOMIN_W_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOMAX_W_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOMINU_W_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP; 
      `AMOMAXU_W_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
       
    `ifdef RV64
      `LR_D_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `SC_D_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP; 
      `AMOSWAP_D_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOADD_D_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOXOR_D_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOAND_D_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOOR_D_INSTR:   if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOMIN_D_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOMAX_D_INSTR:  if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `AMOMINU_D_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP; 
      `AMOMAXU_D_INSTR: if (csrs.csr_misa[0]==1) return MEMORY; else return TRAP;
      `endif
      `endif
    `ifdef muldiv
      `MUL_OPS: if (csrs.csr_misa[12]==1) return MULDIV; else return TRAP;
      `endif
      `ADD_SUB_INSTR: return ALU;
      `SLL_SRA_INSTR: return ALU;
      `SHIFT_AND_INSTR: return ALU; 
      `ifdef RV64
      `ifdef muldiv
      `MULW_INSTR: if (csrs.csr_misa[12]==1) return MULDIV; else return TRAP;
      `DIVW_OPS: if (csrs.csr_misa[12]==1) return MULDIV; else return TRAP;
      `endif
      `ADDW_SUBW_INSTR: return ALU;
      `SRLW_SRAW_INSTR: return ALU;
      `SLLW_INSTR: return ALU;
      `endif
      `LUI_OP: return ALU;
      `BRANCH_INSTR: if(inst[14:12] !=2 || inst[14:12] != 3) return BRANCH; else return TRAP;
      `JALR_INSTR: return JALR;
      `JAL_INSTR: return JAL;
      `URET_INSTR: if(csrs.csr_misa[13]==1) return SYSTEM_INSTR; else return TRAP;
    `ifdef supervisor
      `SRET_INSTR: if (csrs.csr_misa[18]==1 && csrs.prv!=User && (csrs.prv==Machine || (csrs.prv==Supervisor && csrs.csr_mstatus[22]==0))) return SYSTEM_INSTR;
                 else return TRAP;
              `endif
       `MRET_INSTR: if(csrs.prv==Machine) return SYSTEM_INSTR; else return TRAP;
       `WFI_INSTR: if(csrs.csr_mstatus[21] == 0 || csrs.prv == Machine) return WFI; else return TRAP;
       `SFENCE_INSTR: if(csrs.csr_mstatus[20]==0 || csrs.prv == Machine) return MEMORY; else return TRAP;
       `CSR_INSTR: if(funct3!=0 && funct3!=4 && access_is_valid && address_is_valid) return SYSTEM_INSTR; return TRAP;
        default: return TRAP ;
     endcase
  endfunction
   
  (*noinline*)
  function Bit#(`causesize) func_dec_trapcause(Bit#(32) inst, CSRtoDecode csrs);
   `ifdef debug
    Bool ebreakm = unpack(csrs.csr_dcsr[15]);
    Bool ebreaks = unpack(`ifdef supervisor csrs.csr_dcsr[14] `else 0 `endif );
    Bool ebreaku = unpack(`ifdef user csrs.csr_dcsr[13] `else 0 `endif );
  `endif
    case (inst) matches
    `ECALL_INSTR: return (csrs.csr_misa[20]==1 && csrs.prv==User)?`Ecall_from_user: 
                  `ifdef supervisor (csrs.csr_misa[18]==1 && csrs.prv==Supervisor)?`Ecall_from_supervisor: `endif
                                              `Ecall_from_machine;
    `EBREAK_INSTR: `ifdef debug
                    if(                   (ebreakm && csrs.prv == Machine) 
                      `ifdef supervisor || (ebreaks && csrs.prv == Supervisor) `endif 
                      `ifdef user       || (ebreaku && csrs.prv == User)    `endif ) begin
                      let trapcause = `HaltEbreak;
                      trapcause[`causesize - 1] = 1;
                      return trapcause;
                    end
                    
                    else
                  `endif
                    return `Breakpoint;
    default: return `Illegal_inst ;
     endcase
  endfunction  
  (*noinline*)
  function DecodeOut decoder_func_32(Bit#(32) inst, CSRtoDecode csrs
                                    `ifdef compressed , Bool compressed `endif );

    Bit#(1) fs = |csrs.csr_mstatus[14:13];
    Bit#(3) frm = csrs.frm;
    // ------- Default declarations of all local variables -----------//

		Bit#(5) rs1=func_dec_rs1(inst);
		Bit#(5) rs2=func_dec_rs2(inst, csrs);
		Bit#(5) rd =func_dec_rd(inst) ;
		Bit#(5) opcode= inst[6:2];
		Bit#(3) funct3= inst[14:12];
                Bit#(7) funct7 = inst[31:25];
		Bool word32 =False;

		//operand types
		Op1type rs1type=func_dec_rs1type(inst);
		Op2type rs2type=func_dec_rs2type(inst `ifdef compressed , compressed `endif );

    // ------------------------------------------------------------------

    //---------------- Decoding the immediate values-------------------------------------

    // Identify the type of intruction first
    Bool stype= (opcode=='b01000 || (opcode=='b01001 && csrs.csr_misa[5]==1) );
    Bool r4type= (opcode[4:2]=='b100);

    Bit#(32) immediate_value=func_dec_immediate(inst, csrs);
    Access_type mem_access=func_dec_mem_access(inst);


      
    // Following table describes what the ALU will need for some critical operations. Based on this
    // the next set of logic is implemented. rs1+ rs2 is a XLEN bit adder. rs3+ rs4 is `paddr bit
    // adder.
    // Now PC can be present either in rs1 or rs3. This has been done to reduce the mux to the ALU
    // in the next stage. There will only be a mux in the next stage to identify the PC and send it
    // to the next stage.
    //
    //          rs1   rs2   rs3   rs4
    // Branch   OP1   OP2   PC    Imm
    // JAL      PC    'd4   PC    Imm   (rs1=0, rs2=0 since neither required)
    // JALR     PC    'd4   op1   Imm   (rs2=0 since not required)
    // LOAD     PC    op2   op1   Imm   (rs2=0 since not required) // PC needs to be sent as well
    // STORE    PC    op2   op1   Imm   (both required. op2 is the data)
    // AUIPC    PC    Imm   PC    Imm   (rs1=0, rs2=0 since neither required)
    // Atomic   PC    op1   op1    0
    /////////////////////////////////////////////////////////////////////////////////

// ------------------------------------------------------------------------------------------- //
  Bit#(`causesize) trapcause=func_dec_trapcause(inst, csrs);
  Bool valid_rounding = (funct3=='b111)?(frm!='b101 && frm!='b110 && frm!='b111):(funct3!='b101 && funct3!='b110);
	Bool address_is_valid=address_valid(inst[31:20],csrs.csr_misa);
	Bool access_is_valid=valid_csr_access(inst[31:20],inst[19:15], inst[13:12],
                                        	csrs.csr_mstatus[20], csrs.prv);
  Instruction_type inst_type = func_dec_insttype(inst, fs, csrs, valid_rounding);
  if(inst[1:0]!='b11 && inst_type != TRAP)begin
    inst_type=TRAP;
    trapcause=`Illegal_inst;
  end

  // checks: TVM=1 TW=1 TSR=0
// --------------------------------------------------------------------------------------------//

    // --------- Function for ALU -------------
    // In case of Atomic operations as well,  the immediate portion will ensure the right opcode is
    // sent to the cache for operations.
		Bit#(4) fn=0;
    `ifdef atomic
    if( opcode==`ATOMIC_op )begin
      if((inst[27]|inst[28]) == 1)
        fn={inst[29:27],1'b1};
      else
        fn={inst[31:29],inst[27]};
    end
    `endif
		if(opcode==`BRANCH_op )begin
			if(funct3[2]==0)
				fn={2'b0,1,funct3[0]};
			else
				fn={1'b1,funct3};
		end
		else if(`ifdef RV64 opcode==`IMM_ARITHW_op || `endif opcode==`IMM_ARITH_op )begin
			fn=case(funct3)
				'b010: 'b1100;
				'b011: 'b1110;
				'b101: if(funct7[5]==1) 'b1011; else 'b0101;
				default:{1'b0,funct3};
			endcase;
		end
		else if(`ifdef RV64 opcode==`ARITHW_op || `endif opcode==`ARITH_op )begin
			fn=case(funct3)
				'b000:if(funct7[5]==1) 'b1010; else 'b0000;
				'b010:'b1100;
				'b011:'b1110;
				'b101:if (funct7[5]==1) 'b1011;else 'b0101;
				default:{1'b0,funct3};
			endcase;
		end
    else if(opcode[4:3]=='b10 && (csrs.csr_misa[5]|csrs.csr_misa[3])==1) // floating point instructions
	  		fn=opcode[3:0];
    // ---------------------------------------

    if(inst_type==SYSTEM_INSTR)
      immediate_value={'d0,inst[19:15],immediate_value[11:0]};// TODO fix this
  `ifdef spfpu
    if(inst_type==FLOAT && funct3=='b111)
      funct3=frm;
  `endif
    Bit#(7) temp1 = {fn,funct3};
    if(inst_type==TRAP)
      temp1=zeroExtend(trapcause);

    Bool rerun = mem_access==Fence || mem_access==FenceI || inst_type==SYSTEM_INSTR
                `ifdef supervisor || mem_access==SFence `endif ;
  `ifdef spfpu
    Bit#(5) rs3=func_dec_rs3(inst);
    RFType rs3type=func_dec_rs3type(inst);
    RFType rdtype=func_dec_rdtype(inst);
  `endif
    
    let op_addr = OpAddr{rs1addr:rs1, rs2addr:rs2, rd:rd
            `ifdef spfpu ,rs3addr: rs3 `endif };
    let op_type = OpType{rs1type: rs1type, rs2type:rs2type
          `ifdef spfpu ,rs3type: rs3type, rdtype: rdtype `endif };
    let instr_meta = InstrMeta{inst_type: inst_type, memaccess: mem_access,funct:temp1,
                              immediate: immediate_value, rerun:rerun};
    return DecodeOut{op_addr:op_addr, op_type:op_type, meta:instr_meta
                    `ifdef compressed , compressed:False `endif };

  endfunction

  (*noinline*)
  function Bool decode_word32 (Bit#(32) inst, Bit#(1) misa_c);
    Bool word32=False;
    `ifdef RV64
		  Bit#(5) opcode= inst[6:2];
      Bit#(7) funct7 = inst[31:25];
      if(misa_c==1 && inst[1:0]!='b11)begin
        Quadrant quad =unpack(inst[1:0]);
        Bit#(3) funct3 = inst[15:13];
        if( quad ==Q1 && (funct3=='b001 || (funct3=='b100 && inst[12:10]=='b111 && inst[6]=='b0)))
          word32=True;
      end
      else begin
		    Bit#(3) funct3= inst[14:12];
  		  if(opcode==`IMM_ARITHW_op || opcode==`MULDIVW_op ||  opcode==`ARITHW_op ||
            `ifdef spfpu (opcode[4:3]=='b10 && funct7[0]==0)|| `endif
            (opcode[4:1]=='b0101 && funct3[0]==0))
      	word32=True;
      end
    `endif
    return word32;
  endfunction

  function ActionValue#(DecodeOut) decoder_func(Bit#(32) inst, Bool trap
								`ifdef compressed , Bool compressed `endif ,
                Bit#(`causesize) cause, CSRtoDecode csrs, Bool curr_rerun,
                Bool rerun_fencei `ifdef supervisor ,Bool rerun_sfence `endif
                `ifdef debug , DebugStatus debug, Bool step_done `endif ) =  actionvalue
      DecodeOut result_decode = decoder_func_32(inst, csrs `ifdef compressed ,compressed `endif );
      let {icause, takeinterrupt} = chk_interrupt( csrs.prv, 
                                                   csrs.csr_mstatus,
                                                   csrs.csr_mip, 
                                                   csrs.csr_mie 
                                `ifdef non_m_traps ,csrs.csr_mideleg `endif
                `ifdef supervisor `ifdef usertraps ,csrs.csr_sideleg `endif `endif
                                  `ifdef debug     ,debug, step_done `endif );
      Bit#(7) func_cause=result_decode.meta.funct;
      Instruction_type x_inst_type = result_decode.meta.inst_type;
      Op1type x_rs1type = result_decode.op_type.rs1type;
      Op2type x_rs2type = result_decode.op_type.rs2type;
      Bit#(5) x_rs1addr = result_decode.op_addr.rs1addr;
      Bit#(5) x_rs2addr = result_decode.op_addr.rs2addr;

      if(curr_rerun)begin
        x_inst_type=TRAP;
        func_cause=rerun_fencei?`IcacheFence : `ifdef supervisor rerun_sfence?`SFence: `endif `Rerun ;
        result_decode.meta.rerun=False;
      end
      else if(takeinterrupt)begin
        func_cause=zeroExtend(icause);
        x_inst_type=TRAP;
      end
      else if(trap) begin
        x_inst_type=TRAP;
        func_cause = zeroExtend(cause) ;
      end

      if(x_inst_type == TRAP)begin
        x_rs2addr=0;
        x_rs1addr=0;
        x_rs2type=IntegerRF;
        if(func_cause == `Inst_access_fault
            `ifdef supervisor ||  func_cause==`Inst_pagefault `endif )
          x_rs1type=PC;
        else
          x_rs1type=IntegerRF;
      end
      result_decode.meta.inst_type=x_inst_type;
      result_decode.meta.funct=func_cause;
      result_decode.op_type.rs1type=x_rs1type;
      result_decode.op_type.rs2type=x_rs2type;
      result_decode.op_addr.rs1addr=x_rs1addr;
      result_decode.op_addr.rs2addr=x_rs2addr;
      return result_decode;

  endactionvalue;
endpackage
