/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_dp_memory.sv>
/// @brief      Dual-port synchronous memory with byte enable inputs
///

`include "scr1_arch_description.svh"
`include "defines.svh"

`ifdef NTTSIM
`include "NTTsrc/defines.sv"
`endif

module scr1_dp_memory
#(
    parameter SCR1_WIDTH    = 32,
    parameter SCR1_SIZE     = `SCR1_IMEM_AWIDTH'h00010000,
    parameter SCR1_NBYTES   = SCR1_WIDTH / 8
)
(
    input   logic                           clk,
	 input   logic                           rst_n,
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

`ifdef NTTSIM
logic start,start_delay;
logic valid_out;
logic [31:0] result[512 : 0];
lane_t lane_in;
lane_t lane_out;
`endif

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
        if (wenbb[0]) begin
            memory_array[addrb][0] <= datab[0+:8];
        end
        if (wenbb[1]) begin
            memory_array[addrb][1] <= datab[8+:8];
        end
        if (wenbb[2]) begin
            memory_array[addrb][2] <= datab[16+:8];
        end
        if (wenbb[3]) begin
            memory_array[addrb][3] <= datab[24+:8];
        end
    end
    if (renb) begin
        qb <= memory_array[addrb];
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
always_ff @(posedge clk or negedge rst_n) begin
   if(!rst_n) begin               // initialize the ram_block;
		$readmemh("./initializemif/w_sqrt_queue.mif",ram_block,14'h400);
		$readmemh("./initializemif/inv_w_sqrt_queue.mif",ram_block,14'h600);
		$readmemh("./initializemif/r1_GauSample.mif",ram_block,14'h800);
		$readmemh("./initializemif/r2_GauSample.mif",ram_block,14'ha00);
		$readmemh("./initializemif/e1_GauSample.mif",ram_block,14'hc00);
		$readmemh("./initializemif/e2_GauSample.mif",ram_block,14'he00);
		$readmemh("./initializemif/e3_GauSample.mif",ram_block,14'h1000);
		$readmemh("./initializemif/message_in.mif",ram_block,14'h3e00);
	end
		 
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


`ifdef NTTSIM


assign start = ram_block[512]== 32'hffffffff;
always_ff @(posedge clk)
begin
	start_delay <= start;
//	$display("start=%b",start);
end
logic resetn;

initial begin resetn = 1'b0;
@(posedge clk)
	resetn = 1'b1;
end
 
NTT NTT(.rst_n(resetn),.clk(clk),.valid_in(start_delay),.valid_out(valid_out),.*);

logic [6:0] count;
always_ff@(posedge clk or negedge resetn)
begin
	if(!resetn)
		count <=0;
	else if(start && count<64)
	begin
		count <= count +1'b1;
		lane_in[0] <= ram_block[8*count];
		lane_in[1] <= ram_block[8*count + 1];
		lane_in[2] <= ram_block[8*count + 2];
		lane_in[3] <= ram_block[8*count + 3];
		lane_in[4] <= ram_block[8*count + 4];
		lane_in[5] <= ram_block[8*count + 5];
		lane_in[6] <= ram_block[8*count + 6];
		lane_in[7] <= ram_block[8*count + 7];
	end
	else begin
		for(int i =0; i<8 ; i++)
			lane_in[i] <= {32{1'bx}};
	end


end

int file;

initial begin
file = $fopen("result.txt","wb");
end

logic [6:0] count_out;
always_ff@(posedge clk or negedge resetn)
begin
	if(!resetn)
		count_out <= 0;
	else if(valid_out && count_out<64)
	begin
		count_out <= count_out +1'b1;

		$fdisplay(file,"%h",lane_out[0]);
		$fdisplay(file,"%h",lane_out[1]);
		$fdisplay(file,"%h",lane_out[2]);
		$fdisplay(file,"%h",lane_out[3]);
		$fdisplay(file,"%h",lane_out[4]);
		$fdisplay(file,"%h",lane_out[5]);
		$fdisplay(file,"%h",lane_out[6]);
		$fdisplay(file,"%h",lane_out[7]);

		result[8 * count_out+1] <= lane_out[0]; 
		result[8 * count_out+2] <= lane_out[1]; 
		result[8 * count_out+3] <= lane_out[2]; 
		result[8 * count_out+4] <= lane_out[3]; 
		result[8 * count_out+5] <= lane_out[4]; 
		result[8 * count_out+6] <= lane_out[5]; 
		result[8 * count_out+7] <= lane_out[6]; 
		result[8 * count_out+8] <= lane_out[7]; 

	end
	else if(count_out == 64)
		$fclose(file);		

end

`endif


endmodule : scr1_dp_memory
