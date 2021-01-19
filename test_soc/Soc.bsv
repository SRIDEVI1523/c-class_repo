//See LICENSE.iitm for license details
/* 

Author: Neel Gala
Email id: neelgala@gmail.com
Details:

--------------------------------------------------------------------------------------------------
*/
package Soc;
  // project related imports
	import Semi_FIFOF:: *;
	import AXI4_Types:: *;
	import AXI4_Fabric:: *;
  import ccore:: * ;
  import ccore_types:: * ;
  import Clocks :: *;
  `include "ccore_params.defines"
  `include "Soc.defines"

  // peripheral imports
  import uart::*;
  import clint::*;
  import sign_dump::*;
  import err_slave::*;
  // package imports
  import Connectable:: *;
  import GetPut:: *;
  import Vector::*;
  import bram :: *;
  import bootrom :: *;
  import debug_halt_loop::*;

`ifdef debug
  import debug_types::*;                                                                          
`endif

  typedef 0 Sign_master_num;
  typedef (TAdd#(Sign_master_num, 1)) Mem_master_num;
  typedef (TAdd#(Mem_master_num, 1)) Fetch_master_num;
  typedef (TAdd#(Fetch_master_num, `ifdef debug 1 `else 0 `endif )) Debug_master_num;
  typedef (TAdd#(Debug_master_num, 1)) Num_Masters;
 
    function Bit#(TLog#(`Num_Slaves)) fn_slave_map (Bit#(`paddr) addr);
      Bit#(TLog#(`Num_Slaves)) slave_num = 0;
      if(addr >= `MemoryBase && addr<= `MemoryEnd)
        slave_num = `Memory_slave_num;
      else if(addr>= `BootRomBase && addr<= `BootRomEnd)
        slave_num =  `BootRom_slave_num;
      else if(addr>= `UartBase && addr<= `UartEnd)
        slave_num = `Uart_slave_num;
      else if(addr>= `ClintBase && addr<= `ClintEnd)
        slave_num = `Clint_slave_num;
      else if(addr>= `SignBase && addr<= `SignEnd)
        slave_num = `Sign_slave_num;
      else if(addr>= `DebugBase && addr<= `DebugEnd)
        slave_num = `Debug_slave_num;
      else
        slave_num = `Err_slave_num;
        
      return slave_num;
    endfunction:fn_slave_map

  interface Ifc_Soc;
   `ifdef rtldump
     method Maybe#(CommitLogPacket) dump;
   `endif
    interface RS232 uart_io;
  `ifdef debug
    interface Hart_Debug_Ifc debug_server;
    interface AXI4_Slave_IFC#(`paddr, ELEN, USERSPACE) to_debug_master;
  `endif
  endinterface

  (*synthesize*)
  module mkSoc(Ifc_Soc);
    let curr_clk<-exposeCurrentClock;
    let curr_reset<-exposeCurrentReset;

    AXI4_Fabric_IFC #(Num_Masters, `Num_Slaves, `paddr, ELEN, USERSPACE) 
                                                    fabric <- mkAXI4_Fabric(fn_slave_map);

    Ifc_ccore_axi4 ccore <- mkccore_axi4(`resetpc, 0);
    Ifc_sign_dump signature<- mksign_dump();
  `ifdef debug
    Ifc_debug_halt_loop_axi4#(`paddr, ELEN, USERSPACE) debug_memory <- mkdebug_halt_loop_axi4;
  `endif
	  Ifc_uart_axi4#(`paddr,ELEN,0, 16) uart <- mkuart_axi4(curr_clk,curr_reset, 5);
    Ifc_clint_axi4#(`paddr, ELEN, 0, 1, 2) clint <- mkclint_axi4();
    Ifc_err_slave_axi4#(`paddr,ELEN,0) err_slave <- mkerr_slave_axi4;
    Ifc_bram_axi4#(`paddr, ELEN, USERSPACE, `Addr_space) main_memory <- mkbram_axi4(`MemoryBase,
                                                "code.mem", "MainMEM");
		Ifc_bootrom_axi4#(`paddr, ELEN, USERSPACE, 13) bootrom <-mkbootrom_axi4(`BootRomBase);

    // -------------------------------- JTAG + Debugger Setup ---------------------------------- //
      
    // ------------------------------------------------------------------------------------------//
   	mkConnection(ccore.master_d,	fabric.v_from_masters[valueOf(Mem_master_num)]);
   	mkConnection(ccore.master_i, fabric.v_from_masters[valueOf(Fetch_master_num)]);
   	mkConnection(signature.master, fabric.v_from_masters[valueOf(Sign_master_num) ]);

 	  mkConnection (fabric.v_to_slaves [`Uart_slave_num ],uart.slave);
  	mkConnection (fabric.v_to_slaves [`Clint_slave_num ],clint.slave);
    mkConnection (fabric.v_to_slaves [`Sign_slave_num ] , signature.slave);
    mkConnection (fabric.v_to_slaves [`Err_slave_num ] , err_slave.slave);
  `ifdef debug
    mkConnection (fabric.v_to_slaves [`Debug_slave_num ] , debug_memory.slave);
  `endif
  	mkConnection(fabric.v_to_slaves[`Memory_slave_num] , main_memory.slave);
		mkConnection(fabric.v_to_slaves[`BootRom_slave_num] , bootrom.slave);



    // sideband connection
    mkConnection(ccore.sb_clint_msip,clint.sb_clint_msip);
    mkConnection(ccore.sb_clint_mtip,clint.sb_clint_mtip);
    mkConnection(ccore.sb_clint_mtime,clint.sb_clint_mtime);

    `ifdef rtldump
      interface dump= ccore.dump;
    `endif
    interface uart_io=uart.io;
  `ifdef debug
    interface debug_server = ccore.debug_server;
    interface to_debug_master = fabric.v_from_masters[valueOf(Debug_master_num)];
  `endif

      // ------------- JTAG IOs ----------------------//
      // -------------------------------------------- //
  endmodule: mkSoc
endpackage: Soc
