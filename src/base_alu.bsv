// Copyright (c) 2020 InCore Semiconductors Pvt. Ltd. see LICENSE.incore for more details on licensing terms
/*
Author: Neel Gala, neelgala@incoresemi.com
Created on: Saturday 12 June 2021 01:49:20 PM

*/
/*doc:overview:
This package includes multiple functions for carrying ops from the base RISC-V ISA.

compile-macros:
- base_alu_noinline: When set, causes each function to be synthesized as a separate verilog file.
*/
package base_alu ;
  import FIFOF        :: * ;
  import Vector       :: * ;
  import SpecialFIFOs :: * ;
  import FIFOF        :: * ;
  import BUtils       :: * ;

  import ccore_types  :: * ;

  `include "Logger.bsv"
  `include "decoder.defines"

`ifdef base_alu_noinline
  (*noinline*)
`endif
  /*doc:func: */
  function Bit#(1) fn_bru2 (Bit#(XLEN) op1, Bit#(XLEN) op2, Bit#(4) fn);
    Bit#(XLEN) inv = signExtend(fn[3]);
    let inv_op2 = op2^inv;
    let op1_xor_op2 = op1^inv_op2;
    let adder_output = op1 + inv_op2 + zeroExtend(fn[3]);
    Bit#(1) compare_out = fn[0]^(
            (fn[3] == 0) ? pack(op1_xor_op2 == 0):
            (op1[valueOf(XLEN) - 1] == op2[valueOf(XLEN) - 1]) ? adder_output[valueOf(XLEN) - 1]:
            (fn[1] == 1) ? op2[valueOf(XLEN) - 1] : op1[valueOf(XLEN) - 1]);
    return compare_out;
  endfunction: fn_bru2

`ifdef base_alu_noinline
  (*noinline*)
`endif
  /*doc:func: */
  function Bit#(1) fn_bru (Bit#(XLEN) op1, Bit#(XLEN) op2, Bit#(4) fn);
    Bit#(XLEN) op1_xor_op2 = op1 ^ op2;
    Bit#(1) sign = ~fn[1];
    Bit#(1) adder_z_flag = ~|op1_xor_op2;
    Int#(TAdd#(XLEN, 1)) a = unpack({sign & op1[valueOf(XLEN)-1], op1});
    Int#(TAdd#(XLEN, 1)) b = unpack({sign & op2[valueOf(XLEN)-1], op2});
    Bool less = a < b;
    case (fn)
      `FNSEQ : return adder_z_flag;
      `FNSNE : return ~adder_z_flag;
      `FNSLT, `FNSLTU : return pack(less);
      default: return pack(!less);
    endcase
  endfunction:fn_bru

`ifdef base_alu_noinline
  (*noinline*)
`endif
  /*doc:func: */
  function Bit#(XLEN) fn_add ( Bit#(XLEN) op1, Bit#(XLEN) op2, Bit#(1) sub);
    Bit#(TAdd#(XLEN, 1)) inv = duplicate(pack(sub));
    let inv_op2 = {op2,1'b0}^inv;
    return truncateLSB({op1,1'b1} + inv_op2);
  endfunction: fn_add

`ifdef base_alu_noinline
  (*noinline*)
`endif
  /*doc:func: */
  function Tuple2#(Bit#(1), Bit#(1)) fn_compare (Bit#(XLEN) op1, Bit#(XLEN) op2, Bit#(4) fn, Bit#(XLEN) op1_xor_op2);
    Bit#(1) sign = ~fn[1];
    Bit#(1) adder_z_flag = ~|op1_xor_op2;
    Int#(TAdd#(XLEN, 1)) a = unpack({sign & op1[valueOf(XLEN)-1], op1});
    Int#(TAdd#(XLEN, 1)) b = unpack({sign & op2[valueOf(XLEN)-1], op2});
    Bool less = a < b;
    Bit#(1) branch_taken = case (fn)
      `FNSEQ : adder_z_flag;
      `FNSNE : ~adder_z_flag;
      `FNSLT, `FNSLTU : pack(less);
      default: pack(!less);
    endcase;
    return tuple2(branch_taken, pack(less));
  endfunction: fn_compare

  /*doc:func: */
`ifdef base_alu_noinline
  (*noinline*)
`endif
  function Bit#(XLEN) fn_shift (Bit#(XLEN) op1, Bit#(TLog#(XLEN)) op2, Bit#(4) fn 
                      `ifdef RV64 , Bool wordop `endif );
  `ifdef RV64
	  Bit#(6) shift_amt={((!wordop) ? op2[5] : 0), op2[4 : 0]};
		Bit#(TDiv#(XLEN, 2)) upper_bits = wordop ? signExtend(fn[3] & op1[31]) : op1[63 : 32];
		Bit#(XLEN) shift_inright={upper_bits, op1[31 : 0]};//size of 64 bit
  `else
    Bit#(5) shift_amt = op2[4 : 0];
    Bit#(XLEN) shift_inright = zeroExtend(op1[31 : 0]);//size of 32bit
  `endif
	  let shin = (fn==`FNSR || fn==`FNSRA) ? shift_inright : reverseBits(shift_inright);
	  Int#(TAdd#(XLEN, 1)) t = unpack({(fn[3] & shin[valueOf(XLEN) - 1]), shin});
	  Int#(XLEN) shift_r = unpack(pack(t>>shift_amt)[valueOf(XLEN) - 1 : 0]);//shift right by shift_amt
	  let shift_l = reverseBits(pack(shift_r));//shift left
	  case (fn)
	    `FNSR, `FNSRA: return pack(shift_r);
	    default: return pack(shift_l);
	  endcase
  endfunction: fn_shift

`ifdef base_alu_noinline
  (*noinline*)
`endif
  /*doc:func: */
  function Bit#(XLEN) fn_logic (Bit#(XLEN) op1, Bit#(XLEN) op2, Bit#(4) fn, Bit#(XLEN) op1_xor_op2);
    case (fn)
      `FNOR: return (op1 | op2);
      `FNAND: return (op1 & op2);
      default: return op1_xor_op2;
    endcase
  endfunction: fn_logic

`ifdef base_alu_noinline
  (*noinline*)
`endif
  /*doc:func: */
  function Tuple2#(Bit#(1), Bit#(XLEN)) fn_base_alu (Bit#(XLEN) op1, Bit#(XLEN) op2, Bit#(4) fn
                          , Bit#(XLEN) pc , Bool op1pc `ifdef RV64 , Bool wordop `endif );
    let op1_xor_op2 = op1 ^ op2;
    let lv_add = fn_add(op1pc?pc:op1, op2, fn[1]);
    let {btaken, less} = fn_compare(op1, op2, fn, op1_xor_op2);
    Bit#(XLEN) lv_shiftout = fn_shift(op1, truncate(op2), fn `ifdef RV64 , wordop `endif );
    let lv_logic = fn_logic(op1, op2, fn, op1_xor_op2);
    Bit#(XLEN) aluout = case (fn) 
      `FNADD, `FNSUB: lv_add;
      `FNSLT, `FNSLTU: zeroExtend(pack(less));
      `FNSR, `FNSRA, `FNSL: lv_shiftout;
      default: lv_logic;
    endcase;
    return tuple2(btaken, aluout);
  endfunction: fn_base_alu
endpackage: base_alu

