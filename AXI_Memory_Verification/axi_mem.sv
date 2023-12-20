module my_axi_mem
  #(parameter DATA_WIDTH = 32,
    parameter MEM_SIZE = 128,
    parameter ADDRESS_WIDTH = 32)
  (input aclk,
   input arstn,
   
   //read address channel
   output reg   arready,              //read address ready signal from slave
   input [3:0]  arid,                 //read address id
   input [ADDRESS_WIDTH-1:0] araddr,  //read address signal
   input [3:0]  arlen,                //length of the burst
   input [2:0]  arsize,               //number of bytes in a transfer
   input [1:0]  arburst,              //burst type - fixed, incremental, wrapping
   input        arvalid,              //address read valid signal
  
   
   //read data channel
   output reg [3:0] rid,               //read data id
   output reg [DATA_WIDTH-1:0]rdata,   //read data from slave
   output reg [1:0] rresp,             //read response signal
   output reg rlast,                   //read data last signal
   output reg rvalid,                  //read data valid signal
   input rready,                       //read data ready signal from master  



   //write address channel

  input  awvalid,                      // Write  address valid
  output reg awready,                  // write address ready from slave
  input [3:0] awid,                    // transaction ID
  input [3:0] awlen,                   // burst length
  input [2:0] awsize,                  //burst size
  input [ADDRESS_WIDTH-1:0] awaddr,    //write adress 
  input [1:0] awburst,                 //burst type 

  //write data channel

  input wvalid,                        // Write data signal
  output reg wready,                   // write data ready
  input [3:0] wid,                     // unique id for transaction
  input [DATA_WIDTH-1:0] wdata,        // data
  input [3:0] wstrb,                   // strobe to show which lane have data
  input wlast,                         // write data last signal

  //write response channel

  input bready,                        // Write response ready from master
  output reg bvalid,                   // Write valid response
  output reg [3:0] bid,                // Transaction ID
  output reg [1:0] bresp=0             // Write response

  );
  
  
  parameter AR_IDLE = 0;
  parameter AR_START = 1;
  parameter AR_VALID = 2;
  
  parameter R_IDLE = 0;
  parameter R_START= 1;
  parameter R_WAIT = 2;
  
  parameter AW_IDLE = 0;
  parameter AW_START = 1;
  parameter AW_VALID = 2;


  parameter W_IDLE = 0;
  parameter W_START= 1;
  parameter W_WAIT = 2; 

  parameter B_IDLE = 0;
  parameter B_ACTIVE = 1;

  
  reg [7:0] mem[MEM_SIZE];

  reg [3:0] arlen_t;
  reg [2:0] arsize_t;
  reg [3:0] arid_t;
  reg [1:0] arburst_t;
  reg [ADDRESS_WIDTH-1:0] araddr_t;
  reg [ADDRESS_WIDTH-1:0] araddr_tn;
  
  reg [3:0] awlen_t;
  reg [2:0] awsize_t;
  reg [3:0] awid_t;
  reg [1:0] awburst_t;
  reg [ADDRESS_WIDTH-1:0] awaddr_t;
  reg [ADDRESS_WIDTH-1:0] awaddr_tn;

  int length1=0;
  int w_length=0;
  int w_count=0;
  int count=0;
  int z=0;
  int err=0;
  int s=0;

  reg [1:0] p_arstate,n_arstate;
  reg [1:0] p_rstate,n_rstate;
  reg [1:0] p_awstate,n_awstate;
  reg [1:0] p_wstate,n_wstate;
  reg p_bstate,n_bstate;
  
  
  
 // function to read data in incrment mode 
  function void read_data_incr (input [ADDRESS_WIDTH-1:0] addr, input [2:0] arsize);
      
      unique case(arsize)
        3'b000: begin
          rdata[7:0] = mem[addr];
       end
       
       3'b001: begin
       rdata[7:0]  = mem[addr];
       rdata[15:8] = mem[addr + 1];
       end
       
       3'b010: begin
       rdata[7:0]    = mem[addr];
       rdata[15:8]   = mem[addr + 1];
       rdata[23:16]  = mem[addr + 2];
       rdata[31:24]  = mem[addr + 3];  
       end
            
      endcase
      
  endfunction
  

 // Function to write data in increment mode
  function void write_incr(input [ADDRESS_WIDTH-1:0]addr,input [2:0] awsize,input [3:0] wstrb);
 	  //
	  if(awsize == 3'b010) begin
		  mem[addr] = wdata[7:0];
		  mem[addr+1] = wdata[15:8];
		  mem[addr+2] = wdata[23:16];
		  mem[addr+3] = wdata[31:24];
	  end
	  else if(awsize == 3'b001) begin
		  case(wstrb)
			  3'b0011: begin
				  mem[addr] = wdata[7:0];
				  mem[addr+1] = wdata[15:8];
			  end
			  3'b0110: begin
				  mem[addr] = wdata[15:8];
				  mem[addr+1] = wdata[23:16];
			  end
			  3'b1100: begin
				  mem[addr] = wdata[23:16];
				  mem[addr+1] = wdata[31:24];
			  end
			  3'b0101: begin
				  mem[addr] = wdata[7:0];
				  mem[addr+1] = wdata[23:16];
			  end
			  3'b1001: begin
				  mem[addr] = wdata[7:0];
				  mem[addr+1] = wdata[31:24];
			  end
			  3'b1010: begin
				  mem[addr] = wdata[15:8];
				  mem[addr+1] = wdata[31:24];
			  end
		  endcase
	  end
	  else if(awsize == 3'b000) begin
		  case(wstrb)
                          3'b0001: begin
                                  mem[addr] = wdata[7:0];
                          end
                          3'b0010: begin
                                  mem[addr] = wdata[15:8];
                          end
                          3'b0100: begin
                                  mem[addr] = wdata[23:16];
                          end
                          3'b1000: begin
                                  mem[addr] = wdata[31:24];
                          end
		  endcase
	  end
  endfunction 
  



  /////////////////////////////////////////////////////////////////////////////////// READ OPERATION ///////////////////////////////////////////////////////////////////////////////
  

  always@(posedge aclk or negedge arstn) begin
    if(!arstn) begin
      p_arstate <= AR_IDLE;
      p_rstate <= R_IDLE;
    end
    else begin
      p_arstate <= n_arstate;
      p_rstate <= n_rstate;
    end
  end
  
  //fsm for read address channel
  always@(*) begin	  
    case(p_arstate)
      
      AR_IDLE: begin             //wait for the completion of previous transaction
        arready <=0;
        if(!rvalid) begin
          n_arstate <= AR_START;  //add initial states of all t_registers ///////////////////////////////////////////***************************************************************************
        end
        else begin
          n_arstate <= AR_IDLE;
        end
      end
      
      AR_START:begin            //ready to accept new address
        arready <= 0;
        if(arvalid) begin
          n_arstate <= AR_VALID;
        end
        else begin
          n_arstate <= AR_START;
        end
      end
      
      AR_VALID: begin          //accepts the address and control info
        arlen_t <= arlen;
        arsize_t <= arsize;
        arid_t <= arid;
        araddr_t <= araddr;
        arburst_t <= arburst;
        arready <=1;
        n_arstate <= AR_IDLE;
      end
    endcase
  end
  
 



  //fsm for read data channel
  
  always@(*) begin
    
    case(p_rstate) 
      
      R_IDLE: begin
        rvalid <= 0;
        rlast <= 0;
	rresp <= 0;
	rid <= 0;
        if(p_arstate == AR_VALID) begin
	  araddr_tn=araddr_t;	
          n_rstate <= R_START;
          length1 = 0;
          count = 0;
	  // z is the burst size
          if(arsize_t==0)
                  z=1;
          else if(arsize_t==1)
                  z=2;
          else if(arsize_t==2)
                  z=4;

        end
        else begin
          n_rstate <= R_IDLE;
        end
      end
      
      R_START: begin
        
        //update read data channel signals according to burst type
        if(arburst_t==2'b01) begin
          
          read_data_incr(araddr_tn,arsize_t);
	  araddr_tn <= araddr_t+((length1+1)*z); 
	  //count <= length1;
          length1 <= count+1;
	  rvalid <= 1;
        end   
	rid <= arid_t;

	//response siganl
	if(araddr_tn > MEM_SIZE || arsize_t > 3'b010) begin
		rresp <= 2'b10;
	end
	else
		rresp <= 2'b00;
        
        if(!rready && length1 == arlen_t+1) begin
          n_rstate <= R_WAIT;
          rlast <= 1;
        end
        
        else if(!rready && length1 != arlen_t+1) begin
          n_rstate <= R_WAIT;
          rlast <= 0;
        end
        
        else if(rready && length1 == arlen_t+1) begin
          n_rstate <= R_IDLE;
          rlast <= 1;
        end
        
        else begin
          n_rstate <= R_START;
	  //count = length1;
          rlast <= 0;
        end
      end


       
      R_WAIT: begin
        if(rready) begin
          if(length1 == arlen_t+1) begin
            n_rstate <= R_IDLE; 
            rvalid <= 0;
          end
          else begin
            n_rstate <= R_START;
	   // count <= length1;
          end
        end
        else begin
          n_rstate <= R_WAIT;
	  rvalid <= 1;
        end
      end
      endcase
    end


////////////////////////////////////////////////////////////////////////////////////////////// WRITE OPERATION ////////////////////////////////////////////////////////////////////////////


  always@(posedge aclk or negedge arstn) begin
    if(!arstn) begin
      p_awstate <= AW_IDLE;
      p_wstate <= W_IDLE;
      p_bstate <= B_IDLE;
    end
    else begin
      p_awstate <= n_awstate;
      p_wstate <= n_wstate;
      p_bstate <= n_bstate;
    end
  end


  // Write address channel FSM

  always@(*) begin
    case(p_awstate)

      AW_IDLE: begin          
        awready <=0;

        if(awvalid) begin  // wait for valid data in write address channel(not mandatory)
          n_awstate <= AW_START;

        end
        else begin
          n_awstate <= AW_IDLE;
        end
      end

      AW_START:begin            //ready to accept new address
        awready <= 0;
        if(awvalid) begin
          n_awstate <= AW_VALID;
        end
        else begin
          n_awstate <= AW_START;
        end
      end

      AW_VALID: begin          //accepts the address and control info
        awlen_t <= awlen;
        awsize_t <= awsize;
        awid_t <= awid;
        awaddr_t <= awaddr;
        awburst_t <= awburst;
        awready <=1;
        n_awstate <= AW_IDLE;
      end
    endcase
  end


  // Write data channel FSM

  always@(*) begin
    
    case(p_wstate) 
      
      W_IDLE: begin
        wready <= 0;
	err <=0;
	if(wvalid) begin
		n_wstate <= W_START;
		awaddr_tn <= awaddr_t;
		if(awsize_t==0)
                  s=1;
                else if(awsize_t==1)
                  s=2;
                else if(awsize_t==2)
                  s=4;

	end
	else begin
		n_wstate <= W_IDLE;
	end
      end
        
      W_START: begin
        wready <= 1;
        //write  data to memory according to burst type
	if(wvalid && awburst == 2'b01) begin  // this condition have to nested for multiple burst types
                write_incr(awaddr_tn,awsize_t,wstrb);
                awaddr_tn <= awaddr_t+((w_length+1)*s);
	        //w_count <= w_length;	
                w_length <= w_count+1; 
		if(awid_t != wid) begin
			err <= 1;
		end

        end

	if(wvalid && w_length != awlen_t+1) begin
		n_wstate <= W_START;

        end
	else if(wvalid && w_length == awlen_t+1) begin
		n_wstate <= W_IDLE;
		if(!wlast) begin
			err <= 1;
		end
        end
	else if(!wvalid && w_length == awlen_t+1) begin
		n_wstate <= W_WAIT;
	end
	else
		n_wstate <= W_WAIT;
      end

             
      W_WAIT: begin
        if(wvalid) begin
		n_wstate <= W_START;
	end
	else begin
		n_wstate <= W_WAIT;
	end
      end
    endcase
  end



  // Write response channel FSM
  

  always@(*) begin
    case(p_bstate)
      B_IDLE: begin
        bvalid <= 0;
        if(wlast && wready) begin  //response will be active only after accepting the last data
          n_bstate <= B_ACTIVE;
        end
        else begin
          n_bstate <= B_IDLE;
        end
      end

      B_ACTIVE: begin
        bvalid <= 1;
        bid <= awid_t; //assume master will send next data only after the response of current data
        if(err==0) begin
          bresp <=0;
        end
        else begin
          bresp <= 2;
        end

	if(bready <= 1) begin
          n_bstate <= B_IDLE;
        end
        else begin
	  n_bstate <= B_ACTIVE;	
        end
      end
     endcase
  end


    
  
/////////////////////////////////////////////////////////////////////////////////////////////// PROPERTIES //////////////////////////////////////////////////////////////////////////////////    
 `ifdef VERIFIC

        default clocking @(posedge aclk); endclocking
        default disable iff(!arstn);

	// Assumptions
	burst_type_write:assume property(awburst == 2'b01);
	burst_type_read:assume property(arburst == 2'b01);
	strobes_and_size:assume property($countones(wstrb) == awsize_t+1);
        P_awstate_range:assume property(p_awstate <3 and n_awstate < 3);
        P_wstate_range:assume property(p_wstate <3 and n_wstate < 3);
        P_bstate_range:assume property(p_bstate <2 and n_bstate < 2);
        P_arstate_range:assume property(p_arstate <3 and n_arstate < 3);
        P_rstate_range:assume property(p_rstate <3 and n_rstate < 3);
      
        aw_valid_stable:assume property($fell(awvalid) |-> $fell(awready));
	w_valid_stable:assume property($fell(wvalid) |-> $fell(wready));
	//b_valid_stable:assume property($fell(bvalid) |-> $fell(bready));
	ar_valid_stable:assume property($fell(arvalid) |-> $fell(arready));
	//r_valid_stable:assume property($fell(rvalid) |-> $fell(rready));

        single_length_rtransactions:assume property(arlen == 0); //the tool not supporting the counting of transactions
	single_length_wtransactions:assume property(awlen == 0); //the tool not supporting the counting of transactions


        //cover the write response channel properties
        resp_c1: cover property(bresp == 2'b00);                //okay
        resp_c2: cover property(bresp == 2'b10);                //slave error
	sequence wresp_handshake;
		bvalid && bready;
	endsequence

	resp_c3: cover property(wresp_handshake);             //write response channel handshake
	
	//cover write address channel properties
	sequence aw_handshake;
                awvalid && awready;
        endsequence
	write_address_handshake_c1: cover property(aw_handshake);             //write address channel handshake


	//cover write data channel properties
	sequence w_handshake;
                wvalid && wready;
        endsequence
	write_data_channel_c1: cover property(w_handshake);             //write data channel handshake
	
	//cover read address channel properties
	sequence ar_handshake;
                arvalid && arready;
        endsequence
	read_address_channel_c1: cover property(ar_handshake);             //read address channel handshake
	
	//cover read data channel properties
	sequence r_handshake;
                rvalid && rready;
        endsequence
	read_data_channel_c1: cover property(r_handshake);             //read data channel handshake



	
	///////////////////write transaction//////////////////////////////
	//writing a data to memory location 22
	

	sequence write_address_22;
		(awvalid and awid==1 and awaddr==22 and awsize==2'b001 )[*3] ;
	endsequence
        
	sequence write_data_22_first;
		wvalid and wdata==32'h00003048 and wid==1 and wstrb==4'b0011 and !wlast;
	endsequence
        
	sequence write_data_22_last;
                wvalid  and wdata==32'h00007092 and wid==1 and wstrb==4'b0011 and wlast;
        endsequence

	sequence write_data_22;
		write_address_22 and  write_data_22_last[*2] ##2 bready ;
	endsequence


	wr_c1: cover property(write_data_22);


	///////////////// read transaction ////////////////////////////

	sequence read_address_15;
                (arvalid and rid==1 and araddr==15 and arsize==2'b001 and !rvalid)[*3] ;
        endsequence

        sequence read_data_15;
                 mem[15]==8'h34 and mem[16]==8'hab ;
        endsequence

	rd_c1: cover property(read_address_15 and read_data_15);






	//assertions
	

 `endif	 
          
        
      
        

endmodule
