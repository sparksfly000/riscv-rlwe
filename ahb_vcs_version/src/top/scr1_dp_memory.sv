/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_dp_memory.sv>
/// @brief      Dual-port synchronous memory with byte enable inputs
///

`include "scr1_arch_description.svh"
`include "defines.svh"


module scr1_dp_memory
#(
    parameter SCR1_WIDTH    = 32,
    parameter SCR1_SIZE     = `SCR1_IMEM_AWIDTH'h00010000,
    parameter SCR1_NBYTES   = SCR1_WIDTH / 8
)
(
    input   logic                           clk,
    // Port A
    input   logic                           rena,
    input   logic [$clog2(SCR1_SIZE)-1:2]   addra,
    output  logic [SCR1_WIDTH-1:0]          qa,
    // Port B
    input   logic                           renb,
    input   logic                           wenb,
    input   logic [SCR1_NBYTES-1:0]         webb,
	 input   logic                           w_is_vector,
    input   logic [$clog2(SCR1_SIZE)-1:2]   addrb,
    input   type_vector 			           datab,
    output  type_vector			              qb
);


`ifdef SCR1_TARGET_FPGA_INTEL
//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic [SCR1_NBYTES-1:0][7:0] memory_array [0:(SCR1_SIZE/SCR1_NBYTES)-1];
logic [3:0] wenbb;
//-------------------------------------------------------------------------------
// Port B memory behavioral description
//-------------------------------------------------------------------------------
assign wenbb = {4{wenb}} & webb;
always_ff @(posedge clk) begin
    if (wenb) begin
	 if(w_is_vector) begin
		  for(int i =0; i< `LANE ; i++)
			memory_array[addrb + i] <= datab[i];
		  end
	else begin
        	if (wenbb[0]) begin
            		memory_array[addrb][0] <= datab[0][0+:8];
        	end
       	 	if (wenbb[1]) begin
            		memory_array[addrb][1] <= datab[0][8+:8];
        	end
        	if (wenbb[2]) begin
            		memory_array[addrb][2] <= datab[0][16+:8];
        	end
        	if (wenbb[3]) begin
            		memory_array[addrb][3] <= datab[0][24+:8];
        	end
    	end
    end
    if (renb) begin
	for(int i =0; i< `LANE ; i++) begin
        	qb[i] <= memory_array[addrb + i];
	end

    end
end
//-------------------------------------------------------------------------------
// Port A memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (rena) begin
        qa <= memory_array[addra];
    end
end

`else // SCR1_TARGET_FPGA_INTEL

// CASE: OTHERS - SCR1_TARGET_FPGA_XILINX, SIMULATION, ASIC etc

localparam int unsigned RAM_SIZE_WORDS = SCR1_SIZE/SCR1_NBYTES;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic [SCR1_WIDTH-1:0]                  ram_block [RAM_SIZE_WORDS-1:0];

//-------------------------------------------------------------------------------
// Port A memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (rena) begin
        qa <= ram_block[addra];
    end
end

//-------------------------------------------------------------------------------
// Port B memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (wenb) begin
		  if(w_is_vector) begin
		  for(int i =0; i< `LANE ; i++)
				ram_block[addrb + i] <= datab[i];
		  end
		  else begin
        for (int i=0; i<SCR1_NBYTES; i++) begin
            if (webb[i]) begin
                ram_block[addrb][i*8 +: 8] <= datab[0][i*8 +: 8];
            end
        end
   	 end 
	end
    if (renb) begin
		  for(int i =0; i< `LANE ; i++) begin
        		qb[i] <= ram_block[addrb + i];
		  end
    end
end

`endif // SCR1_TARGET_FPGA_INTEL

endmodule : scr1_dp_memory
