module mealy_seq(
  input in,clk,rst,
  output  out);

  parameter s1=0;
  parameter s2=1;
  parameter s3=2;
  parameter s4=3;
  parameter s5=4;

  reg [2:0] p_state=0;
  reg [2:0] n_state=0;

  always@(posedge clk) begin
    if(rst) begin
      p_state <=s1;
    end

    else begin
      p_state <= n_state;
    end
  end

  always@(p_state or in) begin
    case(p_state)
      s1: begin
        if(in)
          n_state <= s2;
        else
          n_state <= s1;
      end

      s2: begin
        if(in)
          n_state <= s3;
        else
          n_state <= s1;
      end

      s3: begin
        if(in)
          n_state <= s3;
        else
          n_state <= s4;
      end
      
      s4: begin
        if(in)
          n_state <= s2;
        else
          n_state <= s5;
      end

      s5: begin
        if(in)
          n_state <= s2;
        else
          n_state <= s1;
      end
      default:n_state <=s1;
      endcase
    end

  assign out = (p_state==s5) && (in==1)? 1 : 0;



`ifdef VERIFIC

        default clocking @(posedge clk); endclocking
        default disable iff(rst);

        //cover the output conditions
        output_c1: cover property(out==1);
        output_c2: cover property(out==0);

        sequence pattern;
                in==1 ##1 in==1 ##1 in==0 ##1 in==0 ##1 in==1;
        endsequence

        //check if the pattern is correct out become high
        in_asrt1: assert property(pattern |-> out==1);

        //check if the output is high input pattern is 11001 only
        out_asrt2: assert property(out==1 |-> in==1 && $past(in,1)==0 && $past(in,2)==0 && $past(in,3)==1 && $past(in,4)==1);


        //cover the pattern overlapping condition
        output_c3: cover property(out==1 ##4 out==1);


`endif

endmodule

         
