/*
Author: Neel Gala, neelgala@gmail.com
Created on: Wednesday 29 April 2020 10:09:32 AM IST

*/
package DebugSoc ;
  import FIFOF        :: * ;
  import Vector       :: * ;
  import SpecialFIFOs :: * ;
  import FIFOF        :: * ;
  import Soc          :: * ;
  import uart::*;
  import GetPut       :: * ;
  import Connectable  :: * ;
  import jtagdtm::*;          
  import debug_types::*;                                                                                                                                              
  import riscvDebug013::*;     
  import Clocks :: *;
  import ccore_types:: * ;                                                                   



  `include "Logger.bsv"
  interface Ifc_DebugSoc;
    `ifdef rtldump
      interface Get#(DumpType) io_dump;
    `endif
    interface RS232 uart_io;
      // ------------- JTAG IOs ----------------------//
    (*always_enabled,always_ready*)                                                               
    method Action wire_tms(Bit#(1)tms_in);                                                        
    (*always_enabled,always_ready*)                                                               
    method Action wire_tdi(Bit#(1)tdi_in);                                                        
    (*always_enabled,always_ready*)                                                               
    method Bit#(1)wire_tdo;                                                                       
      // ---------------------------------------------//
    interface Reset soc_reset;
  endinterface

  module mkDebugSoc#(Clock tck_clk, Reset trst)(Ifc_DebugSoc);
    
    let curr_clk<-exposeCurrentClock;
    let curr_reset<-exposeCurrentReset;
    
    MakeResetIfc ndm_reset <-mkReset(0,False,curr_clk);            // create a new reset for curr_clk
    Reset derived_reset <- mkResetEither(ndm_reset.new_rst,curr_reset);     // OR default and new_rst

    Ifc_Soc soc <- mkSoc(reset_by derived_reset);
    // null crossing registers to transfer input signals from current_domain to tck domain
    CrossingReg#(Bit#(1)) tdi<-mkNullCrossingReg(tck_clk,0);                                        
    CrossingReg#(Bit#(1)) tms<-mkNullCrossingReg(tck_clk,0);                                        
    // null crossing registers to transfer signals from tck to curr_clock domain.
    CrossingReg#(Bit#(1)) tdo<-mkNullCrossingReg(curr_clk,0,clocked_by tck_clk, reset_by trst);     
                                                                                                    
    Ifc_jtagdtm jtag_tap <- mkjtagdtm(clocked_by tck_clk, reset_by trst);                           
    Ifc_riscvDebug013 debug_module <- mkriscvDebug013();                                           

    // synFIFOs to transact data between JTAG and debug module                                                                                                    
    SyncFIFOIfc#(Bit#(41)) sync_request_to_dm <-mkSyncFIFOToCC(1,tck_clk,trst);                     
    SyncFIFOIfc#(Bit#(34)) sync_response_from_dm <-mkSyncFIFOFromCC(1,tck_clk);                     
                           
    mkConnection (soc.debug_server ,debug_module.hart);
    mkConnection (debug_module.debug_master, soc.to_debug_master);

    rule rl_generate_ndmreset(debug_module.getNDMReset == 1);
      ndm_reset.assertReset;
      `logLevel( debugsoc, 0, $format("DebubSoc: Asserting NDM Reset"))
    endrule
             // ----------- Connect JTAG IOs through null-crossing registers ------ //
    rule assign_jtag_inputs;                                                                                
      jtag_tap.tms_i(tms.crossed);                                                                  
      jtag_tap.tdi_i(tdi.crossed);                                                                  
      jtag_tap.bs_chain_i(0);                                                                       
      jtag_tap.debug_tdi_i(0);                                                                      
    endrule                                                                                         
                                                                                                    
    rule assign_jtag_output;                                                                                 
      tdo <= jtag_tap.tdo(); //  Launched by a register clocked by inverted tck                     
    endrule                                                                                        
            // ------------------------------------------------------------------- //

    // capture jtag tap request into a syncfifo first.                                                                                                                  
    rule connect_tap_request_to_syncfifo;                                                           
      let x<-jtag_tap.request_to_dm;                                                                
      sync_request_to_dm.enq(zeroExtend(x));          

    // send captured synced jtag tap request to the debug module
    endrule                                                                                         
    rule read_synced_request_to_dm;                                                                 
      sync_request_to_dm.deq;                                                                       
      debug_module.dtm.putCommand.put(sync_request_to_dm.first);                                    
    endrule                                                                                         

    // collect debug response into a syncfifo
    rule connect_debug_response_to_syncfifo;                                                        
      let x <- debug_module.dtm.getResponse.get;                                                    
      sync_response_from_dm.enq(x);          
    endrule                                  

    // send synced debug response back to the JTAG
    rule read_synced_response_from_dm;                                                              
      sync_response_from_dm.deq;                                                                    
      jtag_tap.response_from_dm(sync_response_from_dm.first);                                       
    endrule                                                                                         
    method Action wire_tms(Bit#(1)tms_in);                                                        
      tms <= tms_in;                                                                              
    endmethod                                                                                     
    method Action wire_tdi(Bit#(1)tdi_in);                                                        
      tdi <= tdi_in;                                                                              
    endmethod                                                                                     
    method Bit#(1)wire_tdo;                                                                       
      return tdo.crossed();                                                                       
    endmethod
    `ifdef rtldump
      interface io_dump = soc.io_dump;
    `endif
    interface uart_io = soc.uart_io;

    interface soc_reset = derived_reset;
                                                                                                    
  endmodule:mkDebugSoc
endpackage: DebugSoc

