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
