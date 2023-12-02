module fifo
  #(parameter FIFO_DEPTH=16)
  (
          input we,
          input re,
          input rst,
          input clk,
          input [7:0] wdata,
          output reg [7:0] rdata,
          output full,
          output empty
  );
  reg [7:0] mem[FIFO_DEPTH-1:0]; // fifo memory
  reg [3:0] wptr,rptr; // write and read pointer
  int size=0;
  
  always@(posedge clk) begin
    if(rst) begin
      wptr <= 0;
      rptr <= 0;
      size <= 0;
    end
    
    else begin
      if(we && !full) begin
        mem[wptr] <= wdata;
        wptr ++;
        size ++;
      end
      else if(re && !empty) begin
        rdata <= mem[rptr];
        rptr ++;
        size --;
      end
    end
  end
  
  assign full = size==FIFO_DEPTH-1 ? 1'b1 : 1'b0;
  assign empty = size==0 ? 1'b1 : 1'b0;
  
endmodule




`ifdef FORMAL

       //	as_in1: assume property(!we && re);
	//as_in2: assume property(we && !re);
	
	always@(posedge clk) begin
		if(~rst) begin
			a_size: assert (size == 0
                           || size == $past(size)
                           || size == $past(size) + 1
                           || size == $past(size) - 1); //always increment or decrement by one

			
		//	a_in_con1: assert(we && re); 
		 //      	a_in_con2: assert(!we && re);
                        as_in1: assume property(!we && re);
                        as_in2: assume property(we && !re);


			c_full: cover (full && size==FIFO_DEPTH-1); // fifo full condition
			c_empty: cover (empty && size==0); //fifo empty condition
			
		   end
	 end
       


`ifdef VERIFIC

                	ap_rptr: assert property (@(posedge clk) disable iff (rst) re |=> $changed(rptr));
                        ap_wptr: assert property (@(posedge clk) disable iff (rst) we |=> $changed(wptr));  
	
                        ap_rptr: assert property (@(posedge clk) disable iff (rst) !re && !full  |=> $stable(rptr));
                        ap_wptr: assert property (@(posedge clk) disable iff (rst) !we && !empty |=> $stable(wptr));


  

`endif

`endif 
endmodule
