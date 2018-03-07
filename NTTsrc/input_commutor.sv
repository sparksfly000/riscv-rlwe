`include "defines.sv"
module input_commutor(
	//-------------------- input ----------------
	input clk,rst_n,valid_in,
	input lane_t lane_in,
	//-------------------- output ---------------
	output lane_t lane_out,
	output logic valid_out,
	input nttend

);

	logic valid_delay[4:0];
	lane_t lane_delay[3:0];
	lane_t lane_com[1:0];
delay_unit #(0,1,2,3,4,5,6,7) delay_unit1(.lane_in(lane_in),.lane_out(lane_delay[0]),.valid_in(valid_in),.valid_out(valid_delay[0]),.extend(1'b1),.*);
commutor1 commutor1(.lane_in(lane_delay[0]),.lane_out(lane_com[0]),.valid_in(valid_delay[0]),.valid_out(valid_delay[1]),.*);
delay_unit #(7,6,5,4,3,2,1,0) delay_unit2(.lane_in(lane_com[0]),.lane_out(lane_delay[1]),.valid_in(valid_delay[1]),.valid_out(valid_delay[2]),.extend(1'b0),.*);
delay_unit #(0,8,16,24,32,40,48,56) delay_unit3(.lane_in(lane_delay[1]),.lane_out(lane_delay[2]),.valid_in(valid_delay[2]),.valid_out(valid_delay[3]),.extend(1'b1),.*);
commutor0 commutor0(.lane_in(lane_delay[2]),.lane_out(lane_com[1]),.valid_in(valid_delay[3]),.valid_out(valid_delay[4]),.*);
delay_unit #(56,48,40,32,24,16,8,0) delay_unit4(.lane_in(lane_com[1]),.lane_out(lane_out),.valid_in(valid_delay[4]),.valid_out(valid_out),.extend(1'b0),.*);


endmodule

`ifdef TEST
//--------------------- testbench  ----------------------
module input_commutor_tb;

	logic clk,rst_n,valid_in;
	logic valid_out;
	lane_t lane_in;
	lane_t lane_out;

	input_commutor input_commutor(.*);
	initial begin
	clk= 1'b0;
	rst_n = 1'b0;
	#10;
	rst_n = 1'b1;
	end

	always begin
	#5;
	clk = !clk;
	end

	always  begin
	valid_in = 1'b0;
	# 16;
	valid_in = 1'b1;
	# 10;
	valid_in = 1'b0;
	# 4;
		
	end

		always_ff @(posedge clk or negedge rst_n ) begin
			if(!rst_n) begin
					  lane_in[0]<= 0;
					  lane_in[1]<= 1;
					  lane_in[2]<= 2;
					  lane_in[3]<= 3;
					  lane_in[4]<= 4;
					  lane_in[5]<= 5;
					  lane_in[6]<= 6;
					  lane_in[7]<= 7;
			end else if(valid_in) begin
				lane_in[0] <= lane_in[0] + 8;
				lane_in[1] <= lane_in[1] + 8;
				lane_in[2] <= lane_in[2] + 8;
				lane_in[3] <= lane_in[3] + 8;
				lane_in[4] <= lane_in[4] + 8;
				lane_in[5] <= lane_in[5] + 8;
				lane_in[6] <= lane_in[6] + 8;
				lane_in[7] <= lane_in[7] + 8;
			end
		end

endmodule

`endif
