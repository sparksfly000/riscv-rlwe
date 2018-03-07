`include "defines.sv"
module commutor0(
	// --------------- input ----------------
	input clk,rst_n,valid_in,
	lane_t lane_in,
	// --------------- output ---------------
	output lane_t lane_out,
	output logic valid_out,
	input  logic nttend
);

lane_t next_lane;
logic [15 : 0] com_valid;
logic [7 : 0] count;
always_ff @(posedge clk or  negedge rst_n)
begin
	if(!rst_n)
		count <= 0;
	else if(valid_in)
		count <= count + 1'b1;
	if(nttend)
		count <= '0;

end
always_comb
begin
	com_valid = 0;
	case(count>>3)
	0 : com_valid[0] = 1'b1;
	1 : com_valid[1] = 1'b1;
	2 : com_valid[2] = 1'b1;
	3 : com_valid[3] = 1'b1;
	4 : com_valid[4] = 1'b1;
	5 : com_valid[5] = 1'b1;
	6 : com_valid[6] = 1'b1;
	7 : com_valid[7] = 1'b1;
	8 : com_valid[8] = 1'b1;
	9 : com_valid[9] = 1'b1;
	10 : com_valid[10] = 1'b1;
	11 : com_valid[11] = 1'b1;
	12 : com_valid[12] = 1'b1;
	13 : com_valid[13] = 1'b1;
	14 : com_valid[14] = 1'b1;
	15 : com_valid[15] = 1'b1;
	default : com_valid = 0;
	endcase
end

always_comb
begin
	next_lane = lane_in;
	case(com_valid)
	1 : next_lane = lane_in;
	2 : begin
		next_lane[0] = lane_in[1];
		next_lane[1] = lane_in[0];
	    end
	4 : begin
		next_lane[0] = lane_in[2];
		next_lane[2] = lane_in[0];
	    end
	8 : begin
		next_lane[0] = lane_in[3];
		next_lane[1] = lane_in[2];
		next_lane[2] = lane_in[1];
		next_lane[3] = lane_in[0];
	    end
	16: begin
		next_lane[0] = lane_in[4];
		next_lane[1] = lane_in[3];
		next_lane[3] = lane_in[1];
		next_lane[4] = lane_in[0];
	    end
	32: begin
		next_lane[0] = lane_in[5];
		next_lane[1] = lane_in[4];
		next_lane[2] = lane_in[3];
		next_lane[3] = lane_in[2];
		next_lane[4] = lane_in[1];
		next_lane[5] = lane_in[0];
	    end
	64: begin
		next_lane[0] = lane_in[6];
		next_lane[1] = lane_in[5];
		next_lane[2] = lane_in[4];
		next_lane[4] = lane_in[2];
		next_lane[5] = lane_in[1];
		next_lane[6] = lane_in[0];
	    end
	128:begin
		next_lane[0] = lane_in[7];
		next_lane[1] = lane_in[6];
		next_lane[2] = lane_in[5];
		next_lane[3] = lane_in[4];
		next_lane[4] = lane_in[3];
		next_lane[5] = lane_in[2];
		next_lane[6] = lane_in[1];
		next_lane[7] = lane_in[0];
	    end
	 256:begin
		next_lane[1] = lane_in[7];
		next_lane[2] = lane_in[6];
		next_lane[3] = lane_in[5];
		next_lane[5] = lane_in[3];
		next_lane[6] = lane_in[2];
		next_lane[7] = lane_in[1];
	     end
	 512:begin
		next_lane[2] = lane_in[7];
		next_lane[3] = lane_in[6];
		next_lane[4] = lane_in[5];
		next_lane[5] = lane_in[4];
		next_lane[6] = lane_in[3];
		next_lane[7] = lane_in[2];
	     end
	  1024: begin
		next_lane[3] = lane_in[7];
		next_lane[4] = lane_in[6];
		next_lane[6] = lane_in[4];
		next_lane[7] = lane_in[3];
	       end
	  2048:begin
		next_lane[4] = lane_in[7];
		next_lane[5] = lane_in[6];
		next_lane[6] = lane_in[5];
		next_lane[7] = lane_in[4];
	       end
	  4096:begin
		next_lane[5] = lane_in[7];
		next_lane[7] = lane_in[5];
	       end
	  8192:begin
		next_lane[6] = lane_in[7];
		next_lane[7] = lane_in[6];
	  	end
	  default: next_lane = lane_in;
	endcase
end
always_ff @(posedge clk)
begin
	lane_out <= next_lane;
	valid_out <= valid_in;
end
endmodule


/*
// -------------------------- testbench ----------------------------
module commutor0_tb;

	logic clk,rst_n,valid;
	lane_t lane_in;
        lane_t lane_out;

	commutor0 m(.*);

	initial begin
	clk = 1'b0;
	rst_n = 1'b0;
	valid = 1'b0;
	# 10;
	rst_n = 1'b1;
	valid = 1'b1;
	lane_in[0] = 0;
	# 80;
	lane_in[1] = 64;
	# 80;
	lane_in[2] = 64*2;
	# 80;
	lane_in[3] = 64*3;
	# 80;
	lane_in[4] = 64*4;
	# 80;
	lane_in[5] = 64*5;
	# 80;
	lane_in[6] = 64*6;
	# 80;
	lane_in[7] = 64*7;
	end

	always begin
		# 5;
		clk = !clk;
	end

	genvar i;
	generate for(i = 0; i < 8; i++) begin :loop
		always_ff @(posedge clk)
			lane_in[i] <= lane_in[i] + 1'b1;
	end
	endgenerate
endmodule
*/
