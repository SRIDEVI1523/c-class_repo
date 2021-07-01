package mbox;

import ccore_types    :: *;
`include "Logger.bsv"

import combo          :: * ;
import restoring_div  :: * ;
import SpecialFIFOs   :: * ;
import FIFOF          :: * ;
import TxRx           :: * ;

typedef struct{
`ifdef RV64
  Bool wordop ;
`endif
  Bit#(`xlen) in1; 
  Bit#(`xlen) in2;
  Bit#(3) funct3;
}MBoxIn deriving(Bits, FShow, Eq);

typedef struct{
  Bool mul;
  Bool div;
} MBoxRdy deriving(Bits, FShow, Eq);

interface Ifc_mbox;
	method Action ma_inputs(MBoxIn inputs);
  method MBoxRdy mv_ready;
  method TXe#(Bit#(`xlen)) tx_output;
endinterface: Ifc_mbox

`ifdef mbox_noinline
(*synthesize*)
`endif
module mkmbox#(parameter Bit#(`xlen) hartid) (Ifc_mbox);
  String mbox = "";

  Ifc_combo_mul mul_ <- mkcombo_mul;
  Ifc_restoring_div div_ <- mkrestoring_div(hartid);

  FIFOF#(Bool) ff_ordering <- mkSizedFIFOF(max(`MULSTAGES_TOTAL,1));
  TX#(Bit#(`xlen)) tx_mbox_out <- mkTX;

  /*doc:rule: */
  rule rl_capture_output;
    if (ff_ordering.first) begin // mul operation
      if (mul_.mv_output_valid) begin
        let _x <- mul_.mv_output;
        tx_mbox_out.u.enq(_x);
        ff_ordering.deq;
      end
      else
        `logLevel( mbox, 0, $format("MBOX: Waiting for Mul o/p"))
    end
    else if (!ff_ordering.first) begin // div operation
      if (div_.mv_output_valid) begin
        let _x <- div_.mv_output;
        tx_mbox_out.u.enq(_x);
        ff_ordering.deq;
      end
      else
        `logLevel( mbox, 0, $format("MBOX: Waiting for Div o/p"))
    end
  endrule: rl_capture_output

	method Action ma_inputs(MBoxIn inputs);

    if( inputs.funct3[2] == 0 ) begin // Multiplication ops
      `logLevel( mbox, 0, $format("MBOX: To MUL. Op1:%h Op2:%h ", inputs.in1, inputs.in2 ))
      mul_.ma_inputs(inputs.in1, inputs.in2, inputs.funct3 `ifdef RV64 ,inputs.wordop `endif );
      ff_ordering.enq(True);
    end
    if (inputs.funct3[2] == 1) begin
      ff_ordering.enq(False);
      `logLevel( mbox, 0, $format("MBOX: To DIV. Op1:%h Op2:%h sign:%b", inputs.in1, inputs.in2, inputs.in1[valueOf(`xlen)-1] ))
      div_.ma_inputs( inputs.in1, inputs.in2, inputs.funct3 `ifdef RV64 ,inputs.wordop `endif ) ;
    end
  endmethod
  method mv_ready= MBoxRdy{mul: mul_.mv_ready, div: div_.mv_ready};

  method tx_output = tx_mbox_out.e;
endmodule
endpackage


