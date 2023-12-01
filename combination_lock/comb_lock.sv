// Code your design here
/*
parameter bit [9:0]  C0 = 10'b1;
parameter bit [9:0]  C1 = 10'b10;
parameter bit [9:0]  C2 = 10'b100;
parameter bit [9:0]  C3 = 10'b1000;
parameter bit [9:0]  C4 = 10'b10000;
parameter bit [9:0]  C5 = 10'b100000;
parameter bit [9:0]  C6 = 10'b1000000;
parameter bit [9:0]  C7 = 10'b10000000;
parameter bit [9:0]  C8 = 10'b100000000;
parameter bit [9:0]  C9 = 10'b1000000000;




`ifndef PAST_SECOND_DEBUG_STAGE
parameter bit [9:0]  COMBO_FIRST_PART [3:0]  = '{C0,C1,C2,C3};
parameter bit [9:0]  COMBO_SECOND_PART [3:0] = '{C0,C1,C2,C3};
parameter bit [9:0]  COMBO_THIRD_PART [3:0]  = '{C0,C1,C2,C3};
`else 
`ifndef PAST_THIRD_DEBUG_STAGE
parameter bit [9:0]  COMBO_FIRST_PART [3:0]  = '{C2,C7,C3,C3};
parameter bit [9:0]  COMBO_SECOND_PART [3:0] = '{C0,C0,C0,C3};
parameter bit [9:0]  COMBO_THIRD_PART [3:0]  = '{C2,C7,C3,C3};
`else
parameter bit [9:0]  COMBO_FIRST_PART [3:0]  = '{C2,C7,C3,C0};
parameter bit [9:0]  COMBO_SECOND_PART [3:0] = '{C0,C0,C0,C0};
parameter bit [9:0]  COMBO_THIRD_PART [3:0]  = '{C2,C7,C3,C0};
`endif
`endif
*/

parameter [29:0] INTERNAL_COMBO = 30'b000000000100000000001000000000;


module decoder (
    input clk, rst,
    //input [9:0] digits [3:0],
    input [9:0] digit,
  output reg [29:0] combo
);

    
    reg [9:0] digits_save[2:0];
  
    assign digits_save[0] = digit;
  
    always @(posedge clk or posedge rst) begin
        if (rst) begin
           digits_save[1] <= 0;
           digits_save[2] <= 0;
        end else begin
           digits_save[1] <= digits_save[0];
           digits_save[2] <= digits_save[1];
        end
    end

    // Convert to our binary combo.  To simplify, each 4-digit
    // subfield gets its own 20-bit slot.
   
    always@* begin
      //combo[0:9] <= digits_save[0];
      //combo[10:19] <= digits_save[1];
      //combo[20:29] <= digits_save[2];
      combo <= {digits_save[2],digits_save[1],digits_save[0]};
    end
endmodule

module combination_checker (
    input clk, rst, override,
    input [29:0] combo,
    output reg open
);
    always @(posedge clk or posedge rst) begin
        if (rst) open <= 0;
        else open <= ((combo==INTERNAL_COMBO)||override);
    end

endmodule   


module combination_lock (
    input [9:0] digit, 
    input  override,
    input  clk, rst,
    output reg open
    );

    bit [29:0] combo;
    decoder d1(clk, rst,digit, combo);
    combination_checker cc(clk, rst, override, combo, open);

    // Properties
  /*
    default clocking @(posedge clk); endclocking
    default disable iff (rst);
    Page93_c1: cover property (open == 0);
    Page93_c2: cover property (open == 1);

    genvar i,j;
    generate for (i=0; i<3; i++) begin
        for (j=0; j<9; j++) begin
            Page94_c3: cover property (digits[i][j] == 1);
        end
    end
    endgenerate

    generate for (i = 0; i<4; i++) begin
        Page94_a1: assume property ($onehot(digits[i]));
    end
    endgenerate

    sequence correct_combo_entered;
             (digits == COMBO_FIRST_PART) ##1 
             (digits == COMBO_SECOND_PART) ##1
             (digits == COMBO_THIRD_PART);
    endsequence

    Page95_open_good:  assert property (correct_combo_entered |=> open);
    Page95_open_bad2:  assert property (open |-> $past(digits==COMBO_FIRST_PART,3));
    Page95_open_bad1:  assert property (open |-> $past(digits==COMBO_SECOND_PART,2));
    Page95_open_bad0:  assert property (open |-> $past(digits==COMBO_THIRD_PART,1));

    // Assumption added after first stage of debug
    `ifdef PAST_FIRST_DEBUG_STAGE
    Page99_fix1:  assume property (override == 0);
    `endif

    */

endmodule 


