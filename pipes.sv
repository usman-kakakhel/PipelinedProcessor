`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Alper Karadag, Ziya Erkoc
// 
// Create Date: 03.12.2018 19:22:49
// Design Name: 
// Module Name: pipes
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module SimpleProcessor(input logic clk, bclk, breset,
                       output memwrite, regwrite,
                       output logic[3:0] an,
                       output logic[6:0] C,
                       output logic dp,
                       output logic [7:0] pcO);

        logic clear, clk_pulse, theReset, StallD, StallF, PCSrcM;
	    assign clear = 0;
	    
	    pulse_controller myclkCont(clk, bclk, clear, clk_pulse);
	    
        pulse_controller myresetCont(clk, breset, clear, theReset);
        
     
        logic[31:0] writedata, dataadr, instrD , instrF, pc, ResultW;
        assign pcO[0] = pc[0];
        assign pcO[1] = pc[1];  
        assign pcO[2] = pc[2];  
        assign pcO[3] = pc[3];  
        assign pcO[4] = pc[4];  
        assign pcO[5] = pc[5];  
        assign pcO[6] = pc[6];  
        assign pcO[7] = pc[7];           
 
        mips  myPro(clk_pulse, theReset, instrD, dataadr, ResultW, writedata , pc, instrF, StallD, StallF, PCSrcM, memwrite, regwrite);
        
        logic [3:0] enables;
        assign enables[0] = 1;
        assign enables[1] = 1;
        assign enables[2] = 1;
        assign enables[3] = 1;
        logic [3:0] digit3, digit2, digit1, digit0;
        
        assign digit0 = dataadr[3:0];
        assign digit1 = dataadr[7:4];
        assign digit2 = writedata[3:0];
        assign digit3 = writedata[7:4];
        
        display_controller mydisp(clk, theReset, enables, digit3, digit2, digit1, digit0, an, C, dp);
            

endmodule


////////////////////////////////////////////////////////
//  
//  display_controller.sv
//
//  by Will Sawyer  31 March 2017
//
//  puts 4 hexadecimal values (from O to F) on the 4-digit 7-segment display unit
//     
//
//  the AN, Cx and DP outputs are active-low, for the BASYS3 board
//    AN3 is the left-most digit, AN2 is the second-left-most, etc
//    C[6] is CA for the a segment, c[5] is CB for the b segment, etc
//   
//  Uses the 100 MHz board clock for clk, and uses a clear signal for resetting
//  Takes 4 active-high enable signals, 1 per digit, to enable 
//     or disable display digits
//
//  For correct connections, carefully plan what should be in the .XDC file
//   
//  
////////////////////////////////////////////////////////


module display_controller (
		input logic clk, clear,
		input logic [3:0] enables, 
		input logic [3:0] in3, in2, in1, in0,
		output logic [3:0] AN,
		output logic [6:0] C,
		output logic       DP
		);

		//logic [3:0] current_digit, cur_dig_AN;
		//logic [6:0] segments;
		
      //assign AN = ~(enables & cur_dig_AN);// AN signals are active low on the BASYS3 board,
                                // and must be enabled in order to display the digit
     // assign C = ~segments;     // segments must be inverted, since the C values are active low
     // assign DP = 1;            // makes the dot point always off 
                                // (0 = on, since it is active low)


		
		// divide system clock (100Mhz for Basys3) by 2^N using a counter, which allows us to multiplex at lower speed
        localparam N = 18;
        logic [N-1:0] count = {N{1'b0}}; //initial value
        always@ (posedge clk)
            count <= count + 1;
        
         
        logic [3:0]digit_val; // multiplexer of digits
        logic [3:0]digit_en;  // decoder of enable bits
         
        always_comb
         begin
         digit_en = 4'b1111; 
         digit_val = in0; 
         
          case(count[N-1:N-2]) //using only the 2 MSB's of the counter 
            
           2'b00 :  //select first 7Seg.
            begin
             digit_val = in0;
             digit_en = 4'b1110;
            end
            
           2'b01:  //select second 7Seg.
            begin
             digit_val = in1;
             digit_en = 4'b1101;
            end
            
           2'b10:  //select third 7Seg.
            begin
             digit_val = in2;
             digit_en = 4'b1011;
            end
             
           2'b11:  //select forth 7Seg.
            begin
             digit_val = in3;
             digit_en = 4'b0111;
            end
          endcase
         end
         
        
        //Convert digit value to LED vector. LEDs are active low.
        logic [6:0] sseg_LEDs; 
        always_comb
         begin 
          sseg_LEDs = 7'b1111111; //default
          case(digit_val)
           4'd0 : sseg_LEDs = 7'b1000000; //to display 0
           4'd1 : sseg_LEDs = 7'b1111001; //to display 1
           4'd2 : sseg_LEDs = 7'b0100100; //to display 2
           4'd3 : sseg_LEDs = 7'b0110000; //to display 3
           4'd4 : sseg_LEDs = 7'b0011001; //to display 4
           4'd5 : sseg_LEDs = 7'b0010010; //to display 5
           4'd6 : sseg_LEDs = 7'b0000010; //to display 6
           4'd7 : sseg_LEDs = 7'b1111000; //to display 7
           4'd8 : sseg_LEDs = 7'b0000000; //to display 8
           4'd9 : sseg_LEDs = 7'b0010000; //to display 9
           4'd10: sseg_LEDs = 7'b0001000; //to display a
           4'd11: sseg_LEDs = 7'b0000011; //to display b
           4'd12: sseg_LEDs = 7'b1000110; //to display c
           4'd13: sseg_LEDs = 7'b0100001; //to display d
           4'd14: sseg_LEDs = 7'b0000110; //to display e
           4'd15: sseg_LEDs = 7'b0001110; //to display f   
           default : sseg_LEDs = 7'b0111111; //dash
          endcase
         end
         
        assign AN = digit_en; 
        assign C = sseg_LEDs; 
        assign DP = 1'b1; //turn dp off
         
endmodule



/////////////////////////////////////////////////////////////////////////////////
// 
//   This module takes a slide switch or pushbutton input and 
//   does the following:
//     --debounces it (ignoring any addtional changes for ~40 milliseconds)
//     --synchronizes it with the clock edges
//     --produces just one pulse, lasting for one clock period
//   
//   Note that the 40 millisecond debounce time = 2000000 cycles of 
//   50MHz clock (which has 20 nsec period)
//   
//   sw_input: the signal coming from the slide switch or pushbutton
//   CLK: the 50 MHz system clock on the BASYS2 board
//   clk_pulse: the synchronized debounced single-pulse output
//
//////////////////////////////////////////////////////////////////////////////////

module pulse_controller(
	input CLK, sw_input, clear,
	output reg clk_pulse );

	 reg [2:0] state, nextstate;
	 reg [27:0] CNT; 
	 wire cnt_zero; 

	always @ (posedge CLK, posedge clear)
	   if(clear)
	    	state <=3'b000;
	   else
	    	state <= nextstate;

	always @ (sw_input, state, cnt_zero)
          case (state)
             3'b000: begin if (sw_input) nextstate = 3'b001; 
                           else nextstate = 3'b000; clk_pulse = 0; end	     
             3'b001: begin nextstate = 3'b010; clk_pulse = 1; end
             3'b010: begin if (cnt_zero) nextstate = 3'b011; 
                           else nextstate = 3'b010; clk_pulse = 1; end
             3'b011: begin if (sw_input) nextstate = 3'b011; 
                           else nextstate = 3'b100; clk_pulse = 0; end
             3'b100: begin if (cnt_zero) nextstate = 3'b000; 
                           else nextstate = 3'b100; clk_pulse = 0; end
            default: begin nextstate = 3'b000; clk_pulse = 0; end
          endcase

	always @(posedge CLK)
	   case(state)
		3'b001: CNT <= 100000000;
		3'b010: CNT <= CNT-1;
		3'b011: CNT <= 100000000;
		3'b100: CNT <= CNT-1;
	   endcase

//  reduction operator |CNT gives the OR of all bits in the CNT register	
	assign cnt_zero = ~|CNT;

endmodule



// Define pipes that exist in the PipelinedDatapath. 
// The pipe between Writeback (W) and Fetch (F), as well as Fetch (F) and Decode (D) is given to you.
// Create the rest of the pipes where inputs follow the naming conventions in the book.


module PipeFtoD(input logic[31:0] instr, PcPlus4F,
                input logic EN, clk,clear, reset,		// StallD will be connected as this EN
                output logic[31:0] instrD, PcPlus4D);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset | clear)begin
            instrD <= 0;
            PcPlus4D <= 0;
        end
        else if(EN)
            begin
            instrD<=instr;
            PcPlus4D<=PcPlus4F;
            end
        else begin
            instrD <= instrD;
            PcPlus4D <= PcPlus4D;
        end
    end
endmodule

// Similarly, the pipe between Writeback (W) and Fetch (F) is given as follows.

module PipeWtoF(input logic[31:0] PC,
                input logic EN, clk, reset,		// StallF will be connected as this EN
                output logic[31:0] PCF);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset)
            PCF <= 0;
        else if(EN)
            begin
            PCF<=PC;
            end
        else 
            PCF <= PCF;
    end
endmodule

// *******************************************************************************
// Below, you are given the argument lists of the modules PipeDtoE, PipeEtoM, PipeMtoW.
// You should implement them by looking at pipelined processor image given to you.   
// Don't forget that these codes are tested but you can always make changes if you want.
// Note that some output logics there for debugging purposes, in other words to trace their values in simulation.
// *******************************************************************************


module PipeDtoE(input logic clr, clk, reset, RegWriteD, MemtoRegD, MemWriteD,
                input logic[2:0] AluControlD,
                input logic AluSrcD, RegDstD, BranchD,
                input logic[31:0] RD1D, RD2D,
                input logic[4:0] RsD, RtD, RdD,
                input logic[31:0] SignImmD,
                input logic[31:0] PCPlus4D,
                    output logic RegWriteE, MemtoRegE, MemWriteE,
                    output logic[2:0] AluControlE,
                    output logic AluSrcE, RegDstE, BranchE,
                    output logic[31:0] RD1E, RD2E,
                    output logic[4:0] RsE, RtE, RdE,
                    output logic[31:0] SignImmE,
                    output logic[31:0] PCPlus4E);

    always_ff @(posedge clk, posedge reset)begin
        if (reset | clr)
            begin
                RegWriteE <= 1'b0;
                MemtoRegE <= 1'b0;
                MemWriteE <= 1'b0;
                AluControlE <= 3'b0;
                AluSrcE <= 1'b0;
                RegDstE <= 1'b0;
                BranchE <= 1'b0;
                RD1E <= 32'b0;
                RD2E <= 32'b0;
                RsE <= 5'b0;
                RtE <= 5'b0;
                RdE <= 5'b0;
                SignImmE <= 32'b0;
                PCPlus4E <= 32'b0;
            end
        else 
            begin
                RegWriteE <= RegWriteD;
                MemtoRegE <= MemtoRegD;
                MemWriteE <= MemWriteD;
                AluControlE <= AluControlD;
                AluSrcE <= AluSrcD;
                RegDstE <= RegDstD;
                BranchE <= BranchD;
                RD1E <= RD1D;
                RD2E <= RD2D;
                RsE <= RsD;
                RtE <= RtD;
                RdE <= RdD;
                SignImmE <= SignImmD;
                PCPlus4E <= PCPlus4D;
            end
    end
endmodule

module PipeEtoM(input logic clk,clear, reset, RegWriteE, MemtoRegE, MemWriteE, BranchE, Zero,
                input logic[31:0] ALUOut,
                input logic [31:0] WriteDataE,
                input logic[4:0] WriteRegE,
                input logic[31:0] PCBranchE,
                    output logic RegWriteM, MemtoRegM, MemWriteM, BranchM, ZeroM,
                    output logic[31:0] ALUOutM,
                    output logic [31:0] WriteDataM,
                    output logic[4:0] WriteRegM,
                    output logic[31:0] PCBranchM);
    
    always_ff @(posedge clk, posedge reset) begin
        if (reset | clear)
            begin
                RegWriteM <= 1'b0;
                MemtoRegM <= 1'b0;
                MemWriteM <= 1'b0;
                ZeroM <= 1'b0;
                BranchM <= 1'b0;
                ALUOutM <= 32'b0;
                WriteDataM <= 32'b0;
                WriteRegM <= 5'b0;
                PCBranchM <= 32'b0;
            end
        else 
            begin
                RegWriteM <= RegWriteE;
                MemtoRegM <= MemtoRegE;
                MemWriteM <= MemWriteE;
                ZeroM <= Zero;
                BranchM <= BranchE;
                ALUOutM <= ALUOut;
                WriteDataM <= WriteDataE;
                WriteRegM <= WriteRegE;
                PCBranchM <= PCBranchE;
            end
    end
endmodule

module PipeMtoW(input logic clk, reset, RegWriteM, MemtoRegM,
                input logic[31:0] ReadDataM, ALUOutM,
                input logic[4:0] WriteRegM,
                    output logic RegWriteW, MemtoRegW,
                    output logic[31:0] ReadDataW, ALUOutW,
                    output logic[4:0] WriteRegW);

		always_ff @(posedge clk, posedge reset) begin
            if (reset)
            begin
                RegWriteW <= 1'b0;
                MemtoRegW <= 1'b0;
                ALUOutW <= 32'b0;
                ReadDataW <= 32'b0;
                WriteRegW <= 5'b0;
            end
        else 
            begin
                RegWriteW <= RegWriteM;
                MemtoRegW <= MemtoRegM;
                ALUOutW <= ALUOutM;
                ReadDataW <= ReadDataM;
                WriteRegW <= WriteRegM;
            end
        end
endmodule



// *******************************************************************************
// End of the individual pipe definitions.
// ******************************************************************************

// *******************************************************************************
// Below is the definition of the datapath.
// The signature of the module is given. The datapath will include (not limited to) the following items:
//  (1) Adder that adds 4 to PC
//  (2) Shifter that shifts SignImmE to left by 2
//  (3) Sign extender and Register file
//  (4) PipeFtoD
//  (5) PipeDtoE and ALU
//  (5) Adder for PCBranchM
//  (6) PipeEtoM and Data Memory
//  (7) PipeMtoW
//  (8) Many muxes
//  (9) Hazard unit
//  ...?
// *******************************************************************************

module datapath (input  logic clk, reset,
		         input logic RegWriteD, MemtoRegD, MemWriteD,
		         input logic [2:0] AluControlD,
		         input logic AluSrcD, RegDstD, BranchD,
		             output logic PCSrcM, StallD, StallF,MemWriteM,RegWriteM,
		             output logic[31:0] PCF, instrF, instrD, AluOutM, ResultW, WriteDataM); 
		             
    //outputs from hazard
	logic [1:0] ForwardAE, ForwardBE;	
    //I/O in fetch pipe
    logic [31:0] PC;
    //I/O in Decode pipe
	logic [31:0]  PCPlus4F, PCPlus4D;
	//I/O in Execute pipe
	logic FlushE, RegWriteE, MemtoRegE, MemWriteE,AluSrcE, RegDstE, BranchE;
	logic [2:0] AluControlE;
	logic [31:0] RD1D, RD2D, SignImmD, RD1E, RD2E, SignImmE, PCPlus4E;
	logic [4:0] RsE, RtE, RdE;
	//I/O in Memory pipe
	logic ZeroE,  MemtoRegM,  BranchM, ZeroM;
	logic [31:0]  WriteDataE, PCBranchE, AluOutE, PCBranchM;
	logic [4:0] WriteRegE, WriteRegM;
	//I/O in Write pipe
	logic  RegWriteW, MemtoRegW;
	logic [31:0] ReadDataM, ReadDataW, AluOutW;
	logic [4:0] WriteRegW;
	//extra Execute stage wires
	logic [31:0] SrcAE, SrcBE, ShiftedE;
	
	mux2 #(32) beforeFetchMux(PCPlus4F, PCBranchM,  PCSrcM, PC);
	
	PipeWtoF wtf(PC, ~StallF, clk, reset, PCF);
	//32'b0000_0000_0000_0000_0000_0000_0000_0100
	adder fetchAdder (PCF, 32'b100, PCPlus4F);
	imem im (PCF[31:2], instrF);
	
	PipeFtoD ftd(instrF, PCPlus4F, ~StallD, clk, PCSrcM, reset , instrD, PCPlus4D);
	
	signext decodeExtend (instrD[15:0], SignImmD);
	regfile rf (clk, RegWriteW, instrD[25:21], instrD[20:16], WriteRegW, ResultW, RD1D, RD2D);
	
	PipeDtoE dte(FlushE, clk, reset, RegWriteD, MemtoRegD, MemWriteD, AluControlD, AluSrcD, RegDstD, BranchD, RD1D, RD2D,
	         instrD[25:21], instrD[20:16], instrD[15:11], SignImmD, PCPlus4D, RegWriteE, MemtoRegE, MemWriteE, AluControlE, AluSrcE, RegDstE, 
	         BranchE, RD1E, RD2E, RsE, RtE, RdE, SignImmE, PCPlus4E);
	         
	alu executeALU (SrcAE, SrcBE, AluControlE, AluOutE, ZeroE, reset);
	adder executeAdder (ShiftedE, PCPlus4E, PCBranchE);
	sl2 executeShifter (SignImmE, ShiftedE);
	mux2 #(32) executeMux1 (WriteDataE, SignImmE, AluSrcE, SrcBE);
	mux2 #(5) executeMux2 (RtE, RdE, RegDstE, WriteRegE);
	mux4 #(32) executeMux3 (RD1E, ResultW, AluOutM, 4'b0, ForwardAE, SrcAE);
	mux4 #(32) executeMux4 (RD2E, ResultW, AluOutM, 4'b0, ForwardBE, WriteDataE);
	          
	PipeEtoM etm (clk,PCSrcM, reset , RegWriteE, MemtoRegE, MemWriteE, BranchE, ZeroE, AluOutE, WriteDataE, WriteRegE, PCBranchE,
	        RegWriteM, MemtoRegM, MemWriteM, BranchM, ZeroM, AluOutM, WriteDataM, WriteRegM, PCBranchM);
	        
	dmem dm (clk, MemWriteM, AluOutM, WriteDataM, ReadDataM);
	assign PCSrcM = BranchM & ZeroM;
	       
	PipeMtoW mtw (clk, reset, RegWriteM, MemtoRegM, ReadDataM, AluOutM, WriteRegM, RegWriteW, MemtoRegW, ReadDataW, AluOutW, WriteRegW);
	     
	mux2 #(32) writeMux (AluOutW, ReadDataW, MemtoRegW, ResultW);
	
	
    HazardUnit hazUnit (RegWriteW, WriteRegW, RegWriteM,MemtoRegM, WriteRegM, PCSrcM, RegWriteE,MemtoRegE, RsE,RtE, instrD[25:21], instrD[20:16], ForwardAE, ForwardBE, FlushE, StallD, StallF);

endmodule



// Hazard Unit with inputs and outputs named
// according to the convention that is followed on the book.

module HazardUnit( input logic RegWriteW,
                input logic [4:0] WriteRegW,
                input logic RegWriteM,MemToRegM,
                input logic [4:0] WriteRegM,
                input logic PCSrcM,
                input logic RegWriteE,MemtoRegE,
                input logic [4:0] rsE,rtE,
                input logic [4:0] rsD,rtD,
                output logic [1:0] ForwardAE,ForwardBE,
                output logic FlushE,StallD,StallF);
   
    logic lwstall;
    always_comb begin
        if ((rsE != 0) & (rsE == WriteRegM) & RegWriteM)
            ForwardAE = 2'b10;
        else if ((rsE != 0) & (rsE == WriteRegW) & RegWriteW)
            ForwardAE = 2'b01;
        else
            ForwardAE = 2'b00;
        
        if ((rtE != 0) & (rtE == WriteRegM) & RegWriteM)
            ForwardBE = 2'b10;
        else if ((rtE != 0) & (rtE == WriteRegW) & RegWriteW)
            ForwardBE = 2'b01;
        else
            ForwardBE = 2'b00;
            
        lwstall = ((((rsD == rtE) | (rtD == rtE)) & MemtoRegE) | PCSrcM);
        StallF = lwstall;
        StallD = lwstall;
        FlushE = lwstall;
    
    end

endmodule


module mips (input  logic        clk, reset,
             output  logic[31:0]  instrD,
             output logic[31:0]  AluOutM, ResultW,
             output logic[31:0]  WriteDataM, PCF, instrF,
             output logic StallD, StallF, PCSrcM, MemWriteM, RegWriteM);
    
    logic RegWriteD, MemtoRegD, MemWriteD, jump;
    logic [2:0] AluControlD;
    logic AluSrcD, RegDstD, BranchD;
    

    controller cont (instrD[31:26], instrD[5:0],MemtoRegD, MemWriteD,AluSrcD,RegDstD, RegWriteD,jump,AluControlD,BranchD);
                  
    datapath path (clk, reset,RegWriteD, MemtoRegD, MemWriteD,AluControlD,AluSrcD, RegDstD, BranchD,PCSrcM, StallD, StallF,MemWriteM,RegWriteM,PCF, instrF,instrD, AluOutM, ResultW, WriteDataM); 

endmodule


// External instruction memory used by MIPS single-cycle
// processor. It models instruction memory as a stored-program 
// ROM, with address as input, and instruction as output
// Modify it to test your own programs.

module imem ( input logic [5:0] addr, output logic [31:0] instr);

// imem is modeled as a lookup table, a stored-program byte-addressable ROM
	always_comb
	   case ({addr,2'b00})		   	// word-aligned fetch
//these are all cases given in the lab...
//		address		instruction
//		-------		-----------
		
//		8'h00: instr = 32'h20080007;
//        8'h04: instr = 32'h20090005;
//        8'h08: instr = 32'h200a0000;
//        8'h0c: instr = 32'h210b000f;
//        8'h10: instr = 32'h01095020;
//        8'h14: instr = 32'h01095025;
//        8'h18: instr = 32'h01095024;
//        8'h1c: instr = 32'h01095022;
//        8'h20: instr = 32'h0109502a;
//        8'h24: instr = 32'had280002;
//        8'h28: instr = 32'h8d090000;
//        8'h2c: instr = 32'h1100fff5;
//        8'h30: instr = 32'h200a000a;
//        8'h34: instr = 32'h2009000c;
        
//        8'h00: instr = 32'h20080005;    
//        8'h04: instr = 32'h21090006;
//        8'h08: instr = 32'h01285020;
        
//        8'h00: instr = 32'h20080005;
//        8'h04: instr = 32'h20090006;
//        8'h08: instr = 32'h20040001;
//        8'h0c: instr = 32'h20050002;
//        8'h10: instr = 32'had280000;
//        8'h14: instr = 32'h8d090001;
//        8'h18: instr = 32'h01245020;
//        8'h1c: instr = 32'h01255022;
        
        8'h00: instr = 32'h20090002;
        8'h04: instr = 32'h10000002;
        8'h08: instr = 32'h20090005;
        8'h0c: instr = 32'h21290006;
        8'h10: instr = 32'h20090008;
        8'h14: instr = 32'h20040000;
        8'h18: instr = 32'h20050000;
        8'h1c: instr = 32'hac090000;
	     default:  instr = {32{1'bx}};	// unknown address
	   endcase
endmodule


// 	***************************************************************************
//	Below are the modules that you shouldn't need to modify at all..
//	***************************************************************************

module controller(input  logic[5:0] op, funct,
                  output logic     memtoreg, memwrite,
                  output logic     alusrc,
                  output logic     regdst, regwrite,
                  output logic     jump,
                  output logic[2:0] alucontrol,
                  output logic branch);

   logic [1:0] aluop;

   maindec md (op, memtoreg, memwrite, branch, alusrc, regdst, regwrite, 
         jump, aluop);

   aludec  ad (funct, aluop, alucontrol);

endmodule

// External data memory used by MIPS single-cycle processor

module dmem (input  logic        clk, we,
             input  logic[31:0]  a, wd,
             output logic[31:0]  rd);

   logic  [31:0] RAM[63:0];
  
   assign rd = RAM[a[31:2]];    // word-aligned  read (for lw)

   always_ff @(posedge clk)
     if (we)
       RAM[a[31:2]] <= wd;      // word-aligned write (for sw)

endmodule

module maindec (input logic[5:0] op, 
	              output logic memtoreg, memwrite, branch,
	              output logic alusrc, regdst, regwrite, jump,
	              output logic[1:0] aluop );
   logic [8:0] controls;

   assign {regwrite, regdst, alusrc, branch, memwrite,
                memtoreg,  aluop, jump} = controls;

  always_comb
    case(op)
      6'b000000: controls <= 9'b110000100; // R-type
      6'b100011: controls <= 9'b101001000; // LW
      6'b101011: controls <= 9'b001010000; // SW
      6'b000100: controls <= 9'b000100010; // BEQ
      6'b001000: controls <= 9'b101000000; // ADDI
      6'b000010: controls <= 9'b000000001; // J
      default:   controls <= 9'bxxxxxxxxx; // illegal op
    endcase
endmodule

module aludec (input    logic[5:0] funct,
               input    logic[1:0] aluop,
               output   logic[2:0] alucontrol);
  always_comb
    case(aluop)
      2'b00: alucontrol  = 3'b010;  // add  (for lw/sw/addi)
      2'b01: alucontrol  = 3'b110;  // sub   (for beq)
      default: case(funct)          // R-TYPE instructions
          6'b100000: alucontrol  = 3'b010; // ADD
          6'b100010: alucontrol  = 3'b110; // SUB
          6'b100100: alucontrol  = 3'b000; // AND
          6'b100101: alucontrol  = 3'b001; // OR
          6'b101010: alucontrol  = 3'b111; // SLT
          default:   alucontrol  = 3'bxxx; // ???
        endcase
    endcase
endmodule

module regfile (input    logic clk, we3, 
                input    logic[4:0]  ra1, ra2, wa3, 
                input    logic[31:0] wd3, 
                output   logic[31:0] rd1, rd2);

  logic [31:0] rf [31:0];

  // three ported register file: read two ports combinationally
  // write third port on rising edge of clock. Register0 hardwired to 0.

  always_ff @(negedge clk)
     if (we3) 
         rf [wa3] <= wd3;	

  assign rd1 = (ra1 != 0) ? rf [ra1] : 0;
  assign rd2 = (ra2 != 0) ? rf[ ra2] : 0;

endmodule

module alu(input  logic [31:0] a, b, 
           input  logic [2:0]  alucont, 
           output logic [31:0] result,
           output logic zero, input logic reset);

    always_comb begin
        case(alucont)
            3'b010: result = a + b;
            3'b110: result = a - b;
            3'b000: result = a & b;
            3'b001: result = a | b;
            3'b111: result = (a < b) ? 1 : 0;
            default: result = {32{1'bx}};
        endcase
        if(reset)
            result <= 0;
        end
    
    assign zero = (result == 0) ? 1'b1 : 1'b0;
    
endmodule

module adder (input  logic[31:0] a, b,
              output logic[31:0] y);
     
     assign y = a + b;
endmodule

module sl2 (input  logic[31:0] a,
            output logic[31:0] y);
     
     assign y = {a[29:0], 2'b00}; // shifts left by 2
endmodule

module signext (input  logic[15:0] a,
                output logic[31:0] y);
              
  assign y = {{16{a[15]}}, a};    // sign-extends 16-bit a
endmodule

// parameterized register
module flopr #(parameter WIDTH = 8)
              (input logic clk, reset, 
	       input logic[WIDTH-1:0] d, 
               output logic[WIDTH-1:0] q);

  always_ff@(posedge clk, posedge reset)
    if (reset) q <= 0; 
    else       q <= d;
endmodule


// paramaterized 2-to-1 MUX
module mux2 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1,  
              input  logic s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s ? d1 : d0; 
endmodule

// paramaterized 4-to-1 MUX
module mux4 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1, d2, d3,  
              input  logic[1:0] s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0); 
endmodule

