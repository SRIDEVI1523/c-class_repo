/* 
Copyright (c) 2018, IIT Madras All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted
provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this list of conditions
  and the following disclaimer.  
* Redistributions in binary form must reproduce the above copyright notice, this list of 
  conditions and the following disclaimer in the documentation and/or other materials provided 
 with the distribution.  
* Neither the name of IIT Madras  nor the names of its contributors may be used to endorse or 
  promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS
OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER
IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT 
OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--------------------------------------------------------------------------------------------------

Author: Neel Gala
Email id: neelgala@gmail.com
Details:

--------------------------------------------------------------------------------------------------
*/
package dcache_tb;
  import Vector::*;
  import FIFOF::*;
  import DReg::*;
  import SpecialFIFOs::*;
  import BRAMCore::*;
  import FIFO::*;
  import GetPut::*;
  import dcache_nway::*;
  import test_caches::*;
  //import icache_dm::*;
  import cache_types::*;
  import mem_config::*;
  import BUtils ::*;
  import RegFile::*;
  import device_common::*;
  import Vector::*;
  
  `define sets 64
  `define word_size 4
  `define block_size 8
  `define addr_width 32
  `define ways 4
  `define repl PLRU

  function Bool isIO(Bit#(`addr_width ) addr, Bool cacheable);
    if(!cacheable)
      return True;
    else if( addr < 4096)
      return True;
    else
      return False;    
  endfunction


  (*synthesize*)
  (*conflict_free="core_req_put,deq_lb"*)
  (*conflict_free="upd_data_into_cache,core_req_put"*)
//  (*preempts="check_hit_or_miss,core_req_put"*) // this is only required is single port rams are instantiated
  module mkdcache(Ifc_dcache_dm#(`word_size , `block_size , `sets , `ways ,32,`addr_width ));
    let ifc();
    mkdcache_dm#(isIO,  False, "PLRU", False, "dual") _temp(ifc);
    return (ifc);
  endmodule

  
  (*synthesize*)
  module mktest(Ifc_test_caches#(4,8,64,4,32,32));
    let ifc();
    mktest_caches _temp(ifc);
    return (ifc);
  endmodule

  (*synthesize*)
  module mkdcache_tb(Empty);

  let dcache <- mkdcache();
  let testcache<- mktest();

  RegFile#(Bit#(10), Bit#(TAdd#(TAdd#(TMul#(`word_size, 8), 8), `addr_width ) )) stim <- 
                                                                      mkRegFileFullLoad("test.mem");
  RegFile#(Bit#(10), Bit#(1))  e_meta <- mkRegFileFullLoad("gold.mem");
  RegFile#(Bit#(19), Bit#(TMul#(`word_size, 8))) data <- mkRegFileFullLoad("data.mem");

  Reg#(Bit#(32)) index<- mkReg(0);
  Reg#(Bit#(32)) e_index<- mkReg(0);
  Reg#(Maybe#(DMem_read_request#(32))) read_mem_req<- mkReg(tagged Invalid);
  Reg#(Maybe#(DMem_write_request#(32,TMul#(`block_size, TMul#(`word_size ,8))))) 
                                                            write_mem_req <- mkReg(tagged Invalid);
  Reg#(Bit#(8)) rg_read_burst_count <- mkReg(0);
  Reg#(Bit#(8)) rg_write_burst_count <- mkReg(0);
  Reg#(Bit#(32)) rg_test_count <- mkReg(1);

  FIFOF#(Bit#(TAdd#(TAdd#(TMul#(`word_size, 8), 8), `addr_width ) )) ff_req <- mkSizedFIFOF(32);
  `ifdef simulate
    FIFOF#(Bit#(1)) ff_meta <- mkSizedFIFOF(32);
  `endif

    
  let verbosity=`VERBOSITY;

  `ifdef perf
  Vector#(5,Reg#(Bit#(32))) rg_counters <- replicateM(mkReg(0));
  rule performance_counters;
    Bit#(5) incr = dcache.perf_counters;
    for(Integer i=0;i<5;i=i+1)
      rg_counters[i]<=rg_counters[i]+zeroExtend(incr[i]);
  endrule
  `endif

  rule core_req;
    let stime<-$stime;
    if(stime>=(`sets * `ways * 10 + 20)) begin
      let req=stim.sub(truncate(index));
      // read/write : delay/nodelay : Fence/noFence : Null 
      Bit#(8) control = req[`addr_width + 7: `addr_width ];
      Bit#(2) readwrite=control[7:6];
      Bit#(3) size=control[5:3];
      Bit#(1) delay=control[2];
      Bit#(1) fence=control[1];
      Bit#(TAdd#(`addr_width ,  8)) request = truncate(req);
      Bit#(TMul#(`word_size, 8)) writedata=truncateLSB(req);

      if(request!=0) begin // // not end of simulation
        if(request!='1 && delay==0)
          dcache.core_req.put(tuple7(truncate(req),unpack(fence),0, False, readwrite, size, writedata));
        index<=index+1;
        $display($time,"\tTB: Sending core request for addr: %h",req);
      end
      if((fence==0 && delay==0) || request=='1)begin // if not a fence instruction
        ff_req.enq(req);
        `ifdef simulate
          ff_meta.enq(e_meta.sub(truncate(index)));
        `endif
      end
    end
  endrule

  rule end_sim;
    Bit#(TAdd#(`addr_width ,  8)) request = truncate(ff_req.first());
    if(request==0)begin
    `ifdef perf
      for(Integer i=0;i<5;i=i+1)
        $display($time,"\tTB: Counter-",countName(i),": %d",rg_counters[i]);
    `endif
      $display($time, "\tTB: All Tests PASSED. Total TestCount: %d", rg_test_count-1);
      $finish(0);
    end
  endrule

  rule checkout_request(ff_req.first[39:0]=='1);
    ff_req.deq;
    ff_meta.deq;
    rg_test_count<=rg_test_count+1;
    $display($time,"\tTB: ********** Test:%d PASSED****",rg_test_count);
  endrule


  rule core_resp(ff_req.first[39:0]!='1);
    let resp <- dcache.core_resp.get();
    let req = ff_req.first;
    ff_req.deq();
      Bit#(8) control = req[`addr_width + 7: `addr_width ];
      Bit#(2) readwrite=control[7:6];
      Bit#(3) size=control[5:3];
      Bit#(1) delay=control[2];
      Bit#(1) fence=control[1];
      Bit#(TMul#(`word_size, 8)) writedata=truncateLSB(req);

    let expected_data<-testcache.memory_operation(truncate(req),readwrite,size,writedata);
    Bool metafail=False;
    Bool datafail=False;
  
    `ifdef simulate
      let meta <- dcache.meta.get();
      let expected_meta=ff_meta.first();
      ff_meta.deq();
      if(expected_meta!=meta)begin
        $display($time,"\tTB: Meta does not match for Req: %h",req);
        $display($time,"\tTB: Expected Meta: %b Received Meta:%b", expected_meta,meta);
        metafail=True;
    end
    `endif
    if(expected_data!=tpl_1(resp))begin
        $display($time,"\tTB: Output from cache is wrong for Req: %h",req);
        $display($time,"\tTB: Expected: %h, Received: %h",expected_data,tpl_1(resp));
        datafail=True;
    end

    if(metafail||datafail)begin
      $display($time,"\tTB: Test: %d Failed",rg_test_count);
      $finish(0);
    end
    else
      $display($time,"\tTB: Core received correct response: ",fshow(resp)," For req: %h",req);

  endrule

  rule read_mem_request(read_mem_req matches tagged Invalid);
    let req<- dcache.read_mem_req.get;
    read_mem_req<=tagged Valid req;
    $display($time,"\tTB: Memory Read request",fshow(req));
  endrule

  rule read_mem_resp(read_mem_req matches tagged Valid .req);
    let {addr, burst, size}=req;
    if(rg_read_burst_count == burst) begin
      rg_read_burst_count<=0;
      read_mem_req<=tagged Invalid;
    end
    else begin
      rg_read_burst_count<=rg_read_burst_count+1;
      read_mem_req <= tagged Valid tuple3(axi4burst_addrgen(burst,size,2,addr),burst,size); // parameterize
    end
    let v_wordbits = valueOf(TLog#(`word_size));
    Bit#(19) index = truncate(addr>>v_wordbits);
    let dat=data.sub(truncate(index));
    dcache.read_mem_resp.put(tuple2(dat,False));
    $display($time,"\tTB: Memory Read index: %d responding with: %h ",index,dat);
  endrule
  
  rule write_mem_request(write_mem_req matches tagged Invalid);
    let req<- dcache.write_mem_req.get;
    write_mem_req<=tagged Valid req;
    $display($time,"\tTB: Memory Write request",fshow(req));
  endrule

  rule write_mem_resp(write_mem_req matches tagged Valid .req);
    let {addr, burst, size, writedata}=req;
    if(rg_write_burst_count == burst) begin
      rg_write_burst_count<=0;
      write_mem_req<=tagged Invalid;
      dcache.write_mem_resp.put(False);
    end
    else begin
      rg_write_burst_count<=rg_write_burst_count+1;
      let nextdata=writedata>>32;
      write_mem_req <= tagged Valid tuple4(axi4burst_addrgen(burst,size,2,addr),burst,size,nextdata); // parameterize
    end
    
    let v_wordbits = valueOf(TLog#(`word_size));
    Bit#(19) index = truncate(addr>>v_wordbits);
    let loaded_data=data.sub(index);

    Bit#(32) mask = size[1:0]==0?'hFF:size[1:0]==1?'hFFFF:size[1:0]==2?'hFFFFFFFF:'1;
    Bit#(TLog#(`word_size)) shift_amt=addr[v_wordbits-1:0];
    mask= mask<<shift_amt;

    Bit#(32) write_word=~mask&loaded_data|mask&truncate(writedata);
    data.upd(index,write_word);
    $display($time,"\tTB: Updating Memory index: %d with: %h ",index,write_word);
  endrule


  rule extra_line;
    $display("\n",$time);
  endrule

endmodule

endpackage

