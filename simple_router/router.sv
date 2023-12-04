

module rtr(
  input in,
  input clk,
  input rst,
  input rx_ready,
  output [3:0] dst[3:0],
  output reg [3:0] tx_ready);
  
  reg [5:0] data;
  int i,count;
  
  always @(posedge clk) begin
    if(rst)
      data <= 0;
    else begin
      if(rx_ready) begin
        data[5] <= data[4];
        data[4] <= data[3];
        data[3] <= data[2];
        data[2] <= data[1];
        data[1] <= data[0];
        data[0] <= in;
        count=count+1;
      end
      else begin
        if(count != 6) begin
          count <= 0;
          data <= 0;
          tx_ready <= 0;
        end
        else if(count == 6) begin
          for(i=0;i<4;i++) begin
            if(i == data[5:4]) begin
              dst[i] <= data[3:0];
              tx_ready[i] <=1;
            end
            else begin
              dst[i] <= 0;
              tx_ready[i] <=0;
            end
          end //for
        end
      end
    end
  end
  
endmodule
  
