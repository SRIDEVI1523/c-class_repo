// Copyright (c) 2020 InCore Semiconductors Pvt. Ltd. see LICENSE.incore for more details on licensing terms
/*
Author: Neel Gala, neelgala@incoresemi.com
Created on: Friday 18 June 2021 12:34:39 PM

*/
/*doc:overview
This module implements the scoreboard which currently simply implements a single bit per register
indicating if there exists an instruction in the pipeline which has that particular register as its
destination register.

*/
package scoreboard ;
  import FIFOF        :: * ;
  import Vector       :: * ;
  import SpecialFIFOs :: * ;
  import FIFOF        :: * ;

  `include "Logger.bsv"
  import ccore_types  :: * ;

  interface Ifc_scoreboard;
    method Action ma_lock_rd (SBDUpd lock);
    method Action ma_release_rd (SBDUpd rls);
    method SBD mv_board;
  endinterface: Ifc_scoreboard

  /*doc:module: */
`ifdef scoreboard_noinline
  (*synthesize*)
`endif
  module mkscoreboard#(parameter Bit#(XLEN) hartid)(Ifc_scoreboard);

  `ifdef spfpu
    Vector#(64, Array#(Reg#(Bit#(1)))) rg_rf_board <- replicateM(mkCReg(2,0));
  `else
    Vector#(32, Array#(Reg#(Bit#(1)))) rg_rf_board <- replicateM(mkCReg(2,0));
  `endif

    /*doc:method: This method is used to lock a destination register. WAW is prevented by ensuring
    * that the rd of the new instruction is not already locked*/
    method Action ma_lock_rd (SBDUpd lock);
      `logLevel( sboard, 0, $format("[%2d]SBoard Lock for : ",hartid,fshow(lock)))
      let index =  { `ifdef spfpu pack(lock.rdtype), `endif lock.rd};
      if (index !=0 ) 
        rg_rf_board[index][0] <= 1'b1;
    endmethod
    /*doc:method: This method is used to release the lock of a destination register when the
     * instruction has committed.*/
    method Action ma_release_rd (SBDUpd rls);
      `logLevel( sboard, 0, $format("[%2d]SBoard release for : ",hartid,fshow(rls)))
      let index =  { `ifdef spfpu pack(rls.rdtype), `endif rls.rd};
      if (index !=0 ) 
        rg_rf_board[index][1] <= 1'b0;
    endmethod
    /*doc:method: This method provides a peek into the current score-board status */
    method SBD mv_board;
    `ifdef spfpu 
      Bit#(64) _rf; 
    `else
      Bit#(32) _rf; 
    `endif 
      for (Integer i = 0; i< `ifdef spfpu 64 `else 32 `endif ; i = i + 1) begin
        _rf[i] = rg_rf_board[i][0];
      end
      return SBD{rf_board: _rf};
    endmethod
  endmodule:mkscoreboard
endpackage: scoreboard

