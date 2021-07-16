// Copyright (c) 2020 InCore Semiconductors Pvt. Ltd. see LICENSE.incore for more details on licensing terms
/*
Author: Neel Gala, neelgala@incoresemi.com
Created on: Saturday 19 June 2021 08:22:34 PM

*/
/*doc:overview
This module acts as the capturing stage of all execution units and forwards them in program order to
the write-back stage. 

The module employs a basic polling technique which is governed by the value at the head of the FUid
ISB. The FUid indicates which Functional unit - muldiv, float, base-alu, trap, cache, etc - is
supposed to provide the next set instructino which can be forwarded to the write-back stage.

There can be multiple functional units which can be polled in this stage whose write-back function
is quite similar. Thus, this stage also tries to converge the various FUids to Commit Unit ids.
*/
package stage4;
  import FIFOF        :: * ;
  import Vector       :: * ;
  import SpecialFIFOs :: * ;
  import FIFOF        :: * ;
  import TxRx         :: * ;
  import GetPut       :: * ;

  import ccore_types  :: * ;
  import dcache_types :: * ;
  import pipe_ifcs    :: * ;


  `include "Logger.bsv"

  interface Ifc_stage4;
    interface Ifc_s4_rx rx;
    interface Ifc_s4_tx tx;
    interface Ifc_s4_cache cache;
  `ifdef muldiv
    interface Ifc_s4_muldiv s4_mbox;
  `endif
  endinterface:Ifc_stage4

`ifdef stage4_noinline
  (*synthesize*)
`endif
// the following attributes are only required in simulation mode. They basically allows a rule to
// fire which indicates that a stall is observed.
`ifdef simulate
  (*preempts="rl_capture_muldiv, rl_polling_check"*)
  (*preempts="rl_drop_bypass, rl_polling_check"*)
  (*preempts="rl_fwd_baseout, rl_polling_check"*)
  (*preempts="rl_fwd_systemout, rl_polling_check"*)
  (*preempts="rl_fwd_trapout, rl_polling_check"*)
  (*preempts="rl_handle_memory, rl_polling_check"*)
`endif
  /*doc:module:*/
  module mkstage4#(parameter Bit#(XLEN) hartid)(Ifc_stage4);
    /*doc:submodule: The following are the virtual FIFOs connected to the ISBs from the EXE stage*/
    RX#(BaseOut) rx_baseout <- mkRX; 
    RX#(TrapOut) rx_trapout <- mkRX;
    RX#(SystemOut) rx_systemout <- mkRX;
    RX#(MemoryOut) rx_memoryout <- mkRX;
    RX#(FUid) rx_fuid <- mkRX;
    RX#(Bool) rx_drop <- mkRX;
  `ifdef rtldump
    RX#(CommitLogPacket) rx_commitlog <- mkRX;
  `endif
  `ifdef muldiv
    RX#(Bit#(`xlen)) rx_mbox <- mkRX;
  `endif
  
    /*doc:submodule: Following are the virtual FIFOs connected to the ISBs feeding into the
     * write-back stage*/
    TX#(SystemOut) tx_systemout <- mkTX;
    TX#(TrapOut)   tx_trapout <- mkTX;
    TX#(BaseOut)   tx_baseout <- mkTX;
    TX#(WBMemop)   tx_memio <- mkTX;
    TX#(CUid)      tx_fuid <- mkTX;
    TX#(Bool)      tx_drop <- mkTX;
  `ifdef rtldump
    TX#(CommitLogPacket) tx_commitlog <- mkTX;
  `endif
    // fifo to capture the response from the dmem subsystem
    FIFOF#(DMem_core_response#(ELEN,1)) ff_memory_response <- mkBypassFIFOF();
  `ifdef simulate
    /*doc:rule: This rule is only available in simulation mode. If the FUid is available but the
     * respective functional unit's output is not available, then this rule will fire and print a stall
     * signal in the log*/
    rule rl_polling_check(rx_fuid.u.notEmpty);
      `logLevel( stage4, 0, $format("[%2d]STAGE4: PC:%h",hartid,rx_fuid.u.first.pc))
      `logLevel( stage4, 0, $format("[%2d]STAGE4: Waiting for FUnit:",hartid,fshow(rx_fuid.u.first.insttype)))
    endrule:rl_polling_check
  `endif

    /*doc:rule: This rule will simply bypass the instruction to the write-back stage which was
     * previously tagged to be dropped for various reasons.*/
    rule rl_drop_bypass(rx_fuid.u.first.insttype == DROP);
      tx_drop.u.enq(rx_drop.u.first);
      tx_fuid.u.enq(fn_fu2cu(rx_fuid.u.first));
      rx_drop.u.deq;
      rx_fuid.u.deq;
    `ifdef rtldump
      let clogpkt = rx_commitlog.u.first;
      tx_commitlog.u.enq(clogpkt);
      rx_commitlog.u.deq;
    `endif
      `logLevel( stage4, 0, $format("[%2d]STAGE4: PC:%h",hartid,rx_fuid.u.first.pc))
      `logLevel( stage4, 0, $format("[%2d]STAGE4: Buffering DROP",hartid))
    endrule:rl_drop_bypass

    /*doc:rule: This rule will simply bypass the results of instructinos which were executed in the
    * previous stage without any alteration*/
    rule rl_fwd_baseout(rx_fuid.u.first.insttype == BASE);
      tx_baseout.u.enq(rx_baseout.u.first);
      tx_fuid.u.enq(fn_fu2cu(rx_fuid.u.first));
      rx_baseout.u.deq;
      rx_fuid.u.deq;
      `logLevel( stage4, 0, $format("[%2d]STAGE4: PC:%h",hartid,rx_fuid.u.first.pc))
      `logLevel( stage4, 0, $format("[%2d]STAGE4: Buffering Base ALU Output",hartid))
    `ifdef rtldump
      let clogpkt = rx_commitlog.u.first;
      CommitLogReg _pkt =?;
      if (clogpkt.inst_type matches tagged REG .r)
        _pkt = r;
      _pkt.wdata = rx_baseout.u.first.rdvalue;
      clogpkt.inst_type = tagged REG _pkt;
      tx_commitlog.u.enq(clogpkt);
      rx_commitlog.u.deq;
    `endif
    endrule:rl_fwd_baseout

    /*doc:rule: This rule will bypass the system operation as is to the write-back stage where it
    * will be executed. No alteration required in this stage for system operations*/
    rule rl_fwd_systemout(rx_fuid.u.first.insttype == SYSTEM);
      tx_systemout.u.enq(rx_systemout.u.first);
      tx_fuid.u.enq(fn_fu2cu(rx_fuid.u.first));
      rx_systemout.u.deq;
      rx_fuid.u.deq;
      `logLevel( stage4, 0, $format("[%2d]STAGE4: PC:%h",hartid,rx_fuid.u.first.pc))
      `logLevel( stage4, 0, $format("[%2d]STAGE4: Buffering System Output",hartid))
    `ifdef rtldump
      let clogpkt = rx_commitlog.u.first;
      tx_commitlog.u.enq(clogpkt);
      rx_commitlog.u.deq;
    `endif
    endrule:rl_fwd_systemout

    /*doc:rule: This rule will bypass an instructino that was tagged as a trap in the previous
    * stages to the write-back stage which will handle the traps accordingly*/
    rule rl_fwd_trapout(rx_fuid.u.first.insttype == TRAP);
      tx_trapout.u.enq(rx_trapout.u.first);
      tx_fuid.u.enq(fn_fu2cu(rx_fuid.u.first));
      rx_trapout.u.deq;
      rx_fuid.u.deq;
      `logLevel( stage4, 0, $format("[%2d]STAGE4: PC:%h",hartid,rx_fuid.u.first.pc))
      `logLevel( stage4, 0, $format("[%2d]STAGE4: Buffering Trap Output",hartid))
    `ifdef rtldump
      let clogpkt = rx_commitlog.u.first;
      tx_commitlog.u.enq(clogpkt);
      rx_commitlog.u.deq;
    `endif
    endrule:rl_fwd_trapout

    /*doc:rule: This rule handles the collection of the response from the data caches/memory
    * subsytems. 
    * If the memory subsytem indicates a trap then the tx_trapout ISB is enqueued with
    * the relevant information and FUid is now mapped to a TRAP CUid.
    * 
    * If the memory operation was a cached load, then this stage will enqueue the results into the
    * tx_baseout ISB which will simply udpate the registrfile with relevant values
    * 
    * In all other cases of the memory ops (store, atomic, io, etc). the result from the cache is
    * simply forwarded to the write-back where the final commit signal will be initiated.
    * 
    * if D extension is enabled, then nanboxing of single-precision values is also performed here.
    *
    * Note: In case of loads, thoug the CUid changes to base-out the commitLog packet is still
    * tagged as Memory for correct log-keeping
    */
    rule rl_handle_memory(rx_fuid.u.first.insttype == MEMORY && ff_memory_response.notEmpty);
      `logLevel( stage4, 0, $format("[%2d]STAGE4: PC:%h",hartid,rx_fuid.u.first.pc))
      let mem_response = ff_memory_response.first;
      ff_memory_response.deq;
      let epochs = rx_fuid.u.first.epochs;
      let fuid = fn_fu2cu(rx_fuid.u.first);
      let memop = rx_memoryout.u.first;
      
      Bool trap = mem_response.trap;
      Bit#(`causesize) cause = mem_response.cause;

      if (mem_response.epochs != epochs) begin
        `logLevel( stage4, 0, $format("[%2d]STAGE4: Dropping Mem response",hartid))
      end
      else begin
        rx_fuid.u.deq;
        rx_memoryout.u.deq;
      `ifdef rtldump
        rx_commitlog.u.deq;
        let clogpkt = rx_commitlog.u.first;
      `endif
        if (trap) begin
          fuid.insttype = TRAP;
          TrapOut trapout = TrapOut {cause   : cause, 
                                     is_microtrap: False,
                                     mtval : truncate(mem_response.word)};
          tx_trapout.u.enq(trapout);
          tx_fuid.u.enq(fuid);
          `logLevel( stage4, 0, $format("[%2d]STAGE4: Memory responded with trap:",hartid, fshow(trapout)))
        `ifdef rtldump
          tx_commitlog.u.enq(clogpkt);
        `endif
        end
        else if (mem_response.entry_alloc) begin
          let lv_memop = WBMemop{ memaccess: memop.memaccess , io: mem_response.is_io
              `ifdef nanboxing ,nanboxing: memop.nanboxing `endif
              `ifdef atomic ,atomic_rd_data: mem_response.word `endif };
          tx_memio.u.enq(lv_memop);
          fuid.insttype = MEMORY;
          tx_fuid.u.enq(fuid);
          `logLevel( stage4, 0, $format("[%2d]STAGE4: Mem response received:",hartid, fshow(lv_memop)))
        `ifdef rtldump
          tx_commitlog.u.enq(clogpkt);
        `endif
        end
        else begin
          `ifdef dpfpu if (memop.nanboxing == 1 ) response.word[63:32] == '1; `endif
          fuid.insttype = BASE;
          let baseout = BaseOut {rd: rx_fuid.u.first.rd, rdvalue: mem_response.word, epochs: fuid.epochs
                            `ifdef no_wawstalls ,id: ? `endif
                            `ifdef spfpu        ,fflags: 0, rdtype: fuid.rdtype `endif };
        `ifdef no_wawstalls
          baseout.id = fuid.id;
        `endif
          tx_baseout.u.enq(baseout);
          tx_fuid.u.enq(fuid);
          `logLevel( stage4, 0, $format("[%2d]STAGE4: Memory responded with data:",hartid, fshow(baseout)))
        `ifdef rtldump
          if (memop.memaccess == Atomic && !mem_response.entry_alloc && memop.atomicop=='b0111) begin
            clogpkt.inst_type = tagged REG (CommitLogReg{wdata: mem_response.word, rd:
                fuid.rd, irf: `ifdef spfpu (fuid.rdtype==IRF) `else True `endif });
          end
          else begin
            CommitLogMem _pkt = ?;
            if (clogpkt.inst_type matches tagged MEM .p)
              _pkt = p;
            _pkt.commit_data = baseout.rdvalue;
            clogpkt.inst_type = tagged MEM _pkt;
          end
          tx_commitlog.u.enq(clogpkt);
        `endif
        end
      end
    endrule:rl_handle_memory

  `ifdef muldiv
    /*doc:rule: This rule is fired when the FUid points to the muldiv operations. This rule is fired
     * when the mbox has a valid output. It is expected that the mbox provides output in the same
     * order the inputs were provided. 
     * The outputs from the mbox are transfered to the tx_baseout ISB for a regular commit in the
     * write-back stage
    */
    rule rl_capture_muldiv(rx_fuid.u.first.insttype == MULDIV && rx_mbox.u.notEmpty());
      let mbox_result = rx_mbox.u.first;
      let fuid = fn_fu2cu(rx_fuid.u.first);
      rx_mbox.u.deq;
      tx_baseout.u.enq(BaseOut {rd: rx_fuid.u.first.rd, rdvalue: mbox_result, epochs: fuid.epochs
            `ifdef no_wawstalls ,id: fuid.id `endif
            `ifdef spfpu ,fflags: 0, rdtype: IRF `endif });
      fuid.insttype = BASE;
      tx_fuid.u.enq(fuid);
      rx_fuid.u.deq;
      `logLevel( stage4, 0, $format("[%2d]STAGE4: PC:%h",hartid,rx_fuid.u.first.pc))
      `logLevel( stage4, 0, $format("[%2d]STAGE4: Enquing MULDIV Output: ",hartid, fshow(mbox_result)))
    `ifdef rtldump
      let clogpkt = rx_commitlog.u.first;
      CommitLogReg _pkt =?;
      if (clogpkt.inst_type matches tagged REG .r)
        _pkt = r;
      _pkt.wdata = mbox_result;
      clogpkt.inst_type = tagged REG _pkt;
      tx_commitlog.u.enq(clogpkt);
      rx_commitlog.u.deq;
    `endif
    endrule:rl_capture_muldiv
  `endif

    interface rx = interface Ifc_s4_rx
      interface rx_baseout_from_stage3 = rx_baseout.e;
      interface rx_trapout_from_stage3 = rx_trapout.e;
      interface rx_systemout_from_stage3  = rx_systemout.e;
      interface rx_memoryout_from_stage3 = rx_memoryout.e;
      interface rx_fuid_from_stage3 = rx_fuid.e;
      interface rx_drop_from_stage3 = rx_drop.e;
    `ifdef rtldump
      interface rx_commitlog = rx_commitlog.e;
    `endif
    endinterface;

    interface tx = interface Ifc_s4_tx
      interface tx_systemout_to_stage5  = tx_systemout.e;
      interface tx_trapout_to_stage5  = tx_trapout.e;
      interface tx_baseout_to_stage5 = tx_baseout.e;
      interface tx_memio_to_stage5 = tx_memio.e;
      interface tx_fuid_to_stage5 = tx_fuid.e;
      interface tx_drop_to_stage5 = tx_drop.e;
    `ifdef rtldump
      interface tx_commitlog = tx_commitlog.e;
    `endif
    endinterface;
    interface cache = interface Ifc_s4_cache
      interface  memory_response= interface Put
        method Action put (DMem_core_response#(ELEN,1) response)if(ff_memory_response.notFull);
          ff_memory_response.enq(response);
        endmethod
      endinterface;
    endinterface;
  `ifdef muldiv
    interface s4_mbox = interface Ifc_s4_muldiv
      interface rx_mbox_output = rx_mbox.e;
    endinterface;
  `endif
  endmodule:mkstage4
endpackage: stage4

