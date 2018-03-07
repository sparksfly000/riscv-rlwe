`include "defines.sv"
module TwiddleFactor
#(parameter DATA_WIDTH = 32,
	parameter SIZE = 1024,
	parameter ADDR_WIDTH = $clog2(SIZE)
	)	
	(
	//-------------- input -----------------
	input clk,rst_n,
	input valid_in,
	input lane_t lane_in,
	input is_inv_ntt,
	//--------------- output ----------------
	output lane_t lane_out,
	logic valid_out
	);

	
	localparam MR_DELAY = `MR_DELAY;

	logic [ADDR_WIDTH - 1 : 0] index;
	always_ff @(posedge clk or negedge rst_n)
	begin
		if(!rst_n)
			index <= 0;
		else if(valid_in)
			index <= index + 1'b1;
	end

	logic [DATA_WIDTH - 1 : 0] factor[7:1];
	logic [DATA_WIDTH - 1 : 0] inv_factor[7:1];
	logic [DATA_WIDTH - 1 : 0] sel_factor[7:1];
	
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/weigh_1_1.mif")) weigh1(.read_en(valid_in),.read_addr(index),.read_data(factor[1]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/weigh_1_2.mif")) weigh2(.read_en(valid_in),.read_addr(index),.read_data(factor[2]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/weigh_1_3.mif")) weigh3(.read_en(valid_in),.read_addr(index),.read_data(factor[3]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/weigh_1_4.mif")) weigh4(.read_en(valid_in),.read_addr(index),.read_data(factor[4]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/weigh_1_5.mif")) weigh5(.read_en(valid_in),.read_addr(index),.read_data(factor[5]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/weigh_1_6.mif")) weigh6(.read_en(valid_in),.read_addr(index),.read_data(factor[6]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/weigh_1_7.mif")) weigh7(.read_en(valid_in),.read_addr(index),.read_data(factor[7]),.*);



	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/inv_weigh_1_1.mif")) inv_weigh1(.read_en(valid_in),.read_addr(index),.read_data(inv_factor[1]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/inv_weigh_1_2.mif")) inv_weigh2(.read_en(valid_in),.read_addr(index),.read_data(inv_factor[2]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/inv_weigh_1_3.mif")) inv_weigh3(.read_en(valid_in),.read_addr(index),.read_data(inv_factor[3]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/inv_weigh_1_4.mif")) inv_weigh4(.read_en(valid_in),.read_addr(index),.read_data(inv_factor[4]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/inv_weigh_1_5.mif")) inv_weigh5(.read_en(valid_in),.read_addr(index),.read_data(inv_factor[5]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/inv_weigh_1_6.mif")) inv_weigh6(.read_en(valid_in),.read_addr(index),.read_data(inv_factor[6]),.*);
	ROM #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE),.INITIALIZE("./initializemif/inv_weigh_1_7.mif")) inv_weigh7(.read_en(valid_in),.read_addr(index),.read_data(inv_factor[7]),.*);

	logic valid_delay;
	lane_t lane_in_delay;
   logic [DATA_WIDTH - 1 : 0] multiplier;

	assign sel_factor = is_inv_ntt ? inv_factor : factor; 	
	
	always_ff @(posedge clk) begin
		valid_delay <= valid_in;
		lane_in_delay<= lane_in;
	end
   
	assign  multiplier = is_inv_ntt ? `N_inv : 1;
	
	mr_fun i_mr_fun0(
						.clk      (clk),
						.rst_n    (rst_n),
						.U        (multiplier * lane_in_delay[0]),
						.valid_in (valid_delay),
						.Z        (lane_out[0]),
						.valid_out(valid_out)
			);
	

		
   genvar j;
	generate for(j = 1; j < `R; j++) begin :lane
		mr_fun i_mr_fun(
						.clk      (clk),
						.rst_n    (rst_n),
						.U        (sel_factor[j] * lane_in_delay[j]),
						.valid_in (valid_delay[1]),
						.Z        (lane_out[j]),
						.valid_out()
			);

	end
	endgenerate

endmodule

/*
//------------------------------ testbench ---------------------------
module TwiddleFactor_tb;
        parameter DATA_WIDTH = $clog2(`M);
	parameter SIZE = 64;
	parameter ADDR_WIDTH = $clog2(SIZE);
		
	
	logic clk,rst_n;
	logic en;
	logic [ADDR_WIDTH - 1 : 0] index;
	lane_t lane_in;
	lane_t lane_out;

	TwiddleFactor #(.DATA_WIDTH(DATA_WIDTH),.SIZE(SIZE)) TwiddleFactor(.*);
	initial begin
	en = 1'b1;
	clk = 1'b0;
	rst_n = 1'b0;
	#10;
	rst_n = 1'b1;
	index =0;
	end

	always begin
		# 5;
		clk =!clk;
	end

	always_ff @(posedge clk or negedge rst_n)
	begin
		if(!rst_n)
			index <= 0;
		else begin
			index <= index + 1'b1;
			lane_in[0] = {$random}%`M;	
			lane_in[1] = {$random}%`M;	
			lane_in[2] = {$random}%`M;	
			lane_in[3] = {$random}%`M;	
			lane_in[4] = {$random}%`M;	
			lane_in[5] = {$random}%`M;	
			lane_in[6] = {$random}%`M;	
			lane_in[7] = {$random}%`M;	
		end
	end

endmodule
*/
