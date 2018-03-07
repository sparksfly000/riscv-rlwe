`include "defines.sv"
module commutor1(
	// --------------- input ----------------
	input clk,rst_n,valid_in,
	lane_t lane_in,
	// --------------- output ---------------
	output lane_t lane_out,
	output logic valid_out,
	input logic nttend
);

logic [2:0] count;
lane_t next_lane;
always_ff @(posedge clk or negedge rst_n)
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
	next_lane = lane_in;
	case(count)
	0: begin
		next_lane[1] = lane_in[7];
		next_lane[2] = lane_in[6];
		next_lane[3] = lane_in[5];
		next_lane[5] = lane_in[3];
		next_lane[6] = lane_in[2];
		next_lane[7] = lane_in[1];
	   end
	 1:begin
		next_lane[0] = lane_in[1];
		next_lane[1] = lane_in[0];
		next_lane[2] = lane_in[7];
		next_lane[3] = lane_in[6];
		next_lane[4] = lane_in[5];
		next_lane[5] = lane_in[4];
		next_lane[6] = lane_in[3];
		next_lane[7] = lane_in[2];
	   end
	 2:begin
		next_lane[0] = lane_in[2];
		next_lane[2] = lane_in[0];
		next_lane[3] = lane_in[7];
		next_lane[4] = lane_in[6];
		next_lane[6] = lane_in[4];
		next_lane[7] = lane_in[3];
	   end
	  3:begin
		next_lane[0] = lane_in[3];
		next_lane[1] = lane_in[2];
		next_lane[2] = lane_in[1];
		next_lane[3] = lane_in[0];
		next_lane[4] = lane_in[7];
		next_lane[5] = lane_in[6];
		next_lane[6] = lane_in[5];
		next_lane[7] = lane_in[4];
	   end
	  4:begin
		next_lane[0] = lane_in[4];
		next_lane[1] = lane_in[3];
		next_lane[3] = lane_in[1];
		next_lane[4] = lane_in[0];
		next_lane[5] = lane_in[7];
		next_lane[7] = lane_in[5];
	    end
	  5:begin
		next_lane[0] = lane_in[5];
		next_lane[1] = lane_in[4];
		next_lane[2] = lane_in[3];
		next_lane[3] = lane_in[2];
		next_lane[4] = lane_in[1];
		next_lane[5] = lane_in[0];
		next_lane[6] = lane_in[7];
		next_lane[7] = lane_in[6];
	    end
	  6:begin
		next_lane[0] = lane_in[6];
		next_lane[1] = lane_in[5];
		next_lane[2] = lane_in[4];
		next_lane[4] = lane_in[2];
		next_lane[5] = lane_in[1];
		next_lane[6] = lane_in[0];
		next_lane[7] = lane_in[7];
	    end
    7:begin
		next_lane[0] = lane_in[7];
		next_lane[1] = lane_in[6];
		next_lane[2] = lane_in[5];
		next_lane[3] = lane_in[4];
		next_lane[4] = lane_in[3];
		next_lane[5] = lane_in[2];
		next_lane[6] = lane_in[1];
		next_lane[7] = lane_in[0];
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
//--------------------------------------- testbench --------------------------------

module commutor1_tb;

	logic clk,rst_n,valid,valid_com1;
	lane_t lane_in;
	lane_t lane_delay[3:0];
	lane_t lane_com;
	lane_t lane_out;

	delay_unit #(0,8,16,24,32,40,48,56) delay_unit0(.lane_out(lane_delay[0]),.extend(1'b1),.*);
	commutor0 commutor0(.lane_in(lane_delay[0]),.lane_out(lane_delay[1]),.*);
	delay_unit #(56,48,40,32,24,16,8,0) delay_unit1(.lane_in(lane_delay[1]),.lane_out(lane_delay[2]),.extend(1'b0),.*);
	delay_unit #(0,1,2,3,4,5,6,7) delay_unit2(.lane_in(lane_delay[2]),.lane_out(lane_delay[3]),.extend(1'b1),.*);
	commutor1 commutor1(.lane_in(lane_delay[3]),.lane_out(lane_com),.valid(valid_com1),.*);
	delay_unit #(7,6,5,4,3,2,1,0) delay_unit3(.lane_in(lane_com),.extend(1'b0),.*);
	initial begin
	clk = 1'b0;
	rst_n = 1'b0;
	valid = 1'b0;
	# 10;
	rst_n = 1'b1;

	lane_in[0] = 0;
	lane_in[1] = 64;
	lane_in[2] = 128;
	lane_in[3] = 192;
	lane_in[4] = 256;
	lane_in[5] = 320;
	lane_in[6] = 384;
	lane_in[7] = 448;
	# 575;
	valid_com1=1'b1;
	end
	
	always begin
	# 5;
	clk = !clk;
	end

	always  begin
	valid_in = 1'b0;
	repeat(2) @(posedge clk);
	valid_in = 1'b1;
	repeat(1) @(posedge clk);
		
	end
	
	


	genvar j;
	generate for(j=0; j<8; j++) begin: loop
		always_ff @(posedge clk)
		begin
			if(valid_in)
			lane_in[j] <= lane_in[j] + 1'b1;		
		end
	end
	endgenerate

endmodule
*/
