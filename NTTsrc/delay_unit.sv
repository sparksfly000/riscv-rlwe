`include "defines.sv"
module delay_unit(
	//----------------- input -----------------
	input clk,rst_n,valid_in,extend,            // extend = 1'b1 then extend the valid_out, if extend is equal to 1'b0, the cut the valid_out
	lane_t lane_in,
	//----------------- output ----------------
	output lane_t lane_out,
	logic valid_out
);
parameter DELAY0 = 0;
parameter DELAY1 = 1;
parameter DELAY2 = 2;
parameter DELAY3 = 3;
parameter DELAY4 = 4;
parameter DELAY5 = 5;
parameter DELAY6 = 6;
parameter DELAY7 = 7;

logic valid_delay[(DELAY7+DELAY0) * (`DATA_GAP+1) : 0];
logic valid_delay0[DELAY0  : 0];
data_t data_delay0[DELAY0  : 0];
data_t data_delay1[DELAY1  : 0];
data_t data_delay2[DELAY2  : 0];
data_t data_delay3[DELAY3  : 0];
data_t data_delay4[DELAY4  : 0];
data_t data_delay5[DELAY5  : 0];
data_t data_delay6[DELAY6  : 0];
data_t data_delay7[DELAY7  : 0];
logic valid;

genvar j;
generate
assign valid_delay[0] = valid_in;
for(j = 0; j< (DELAY7+DELAY0) *(`DATA_GAP+1); j++) begin : loop
	always_ff @(posedge clk or negedge rst_n) begin
		if(!rst_n) 
			valid_delay[j+1] <= 1'b0;
		else
			valid_delay[j+1] <= valid_delay[j];
	end
end
endgenerate
	
always_comb begin
	if(extend)
		valid_out = valid_in || valid_delay[(DELAY7+DELAY0)*(`DATA_GAP+1)];
	else
		valid_out = valid_in && valid_delay[(DELAY7+DELAY0)*(`DATA_GAP+1)];
end	

assign valid = extend == 1'b1 ? valid_out : valid_in;
	
generate 
assign data_delay0[0] = lane_in[0];
for(j=0; j< DELAY0; j++) begin : loop0
always_ff @(posedge clk) begin	
	if(valid) begin
		data_delay0[j+1] <= data_delay0[j]; 
	end 
end
end
assign lane_out[0] = data_delay0[DELAY0];
endgenerate

generate 
assign data_delay1[0] = lane_in[1];
for(j=0; j< DELAY1; j++) begin : loop1
	always_ff @(posedge clk) 
		if(valid) begin
			data_delay1[j+1] <= data_delay1[j];
		end 	
end
assign lane_out[1] = data_delay1[DELAY1];
endgenerate

generate 
assign data_delay2[0] = lane_in[2];
for(j=0; j< DELAY2; j++) begin : loop2
	always_ff @(posedge clk) 
		if(valid) begin
			data_delay2[j+1] <= data_delay2[j]; 	
		end
end
assign lane_out[2] = data_delay2[DELAY2];
endgenerate

generate 
assign data_delay3[0] = lane_in[3];
for(j=0; j< DELAY3; j++) begin : loop3
	always_ff @(posedge clk) 
		if(valid) begin
			data_delay3[j+1] <= data_delay3[j]; 	
		end
end
assign lane_out[3] = data_delay3[DELAY3];
endgenerate

generate 
assign data_delay4[0] = lane_in[4];
for(j=0; j< DELAY4; j++) begin : loop4
	always_ff @(posedge clk) 
		if(valid) begin
			data_delay4[j+1] <= data_delay4[j]; 	
		end
end
assign lane_out[4] = data_delay4[DELAY4];
endgenerate

generate 
assign data_delay5[0] = lane_in[5];
for(j=0; j< DELAY5; j++) begin : loop5
	always_ff @(posedge clk) 
		if(valid) begin
			data_delay5[j+1] <= data_delay5[j]; 	
		end
end
assign lane_out[5] = data_delay5[DELAY5];
endgenerate

generate 
assign data_delay6[0] = lane_in[6];
for(j=0; j< DELAY6; j++) begin : loop6
	always_ff @(posedge clk) 
		if(valid) begin
			data_delay6[j+1] <= data_delay6[j]; 	
		end
end
assign lane_out[6] = data_delay6[DELAY6];
endgenerate

generate 
assign data_delay7[0] = lane_in[7];
for(j=0; j< DELAY7; j++) begin : loop7
	always_ff @(posedge clk) 
		if(valid) begin
			data_delay7[j+1] <= data_delay7[j]; 	
		end
end
assign lane_out[7] = data_delay7[DELAY7];
endgenerate

endmodule


`ifdef TEST
//------------------------ testbench -------------------

module delay_unit_tb;


	logic clk,rst_n,valid_in,valid_out;
	lane_t lane_in;
	lane_t lane_out;
   
	delay_unit m(.*);

	initial begin
	clk = 1'b0;
	rst_n = 1'b0;
	# 10;
	rst_n = 1'b1;
	end

	always 
	begin
	#5;
	clk = !clk;	
	end
	
	always  begin
	valid_in = 1'b0;
	repeat(2) @(posedge clk);
	valid_in = 1'b1;
	repeat(1) @(posedge clk);
		
	end

	always_ff @(posedge clk or negedge rst_n)
	begin
		if(!rst_n) begin
			lane_in[0] <= 0;
			lane_in[1] <= 1;
			lane_in[2] <= 2;
			lane_in[3] <= 3;
			lane_in[4] <= 4;
			lane_in[5] <= 5;
			lane_in[6] <= 6;
			lane_in[7] <= 7;
		end else if (valid_in) begin
			lane_in[0] <=  lane_in[0] + 8;
			lane_in[1] <=  lane_in[1] + 8;
			lane_in[2] <=  lane_in[2] + 8;
			lane_in[3] <=  lane_in[3] + 8;
			lane_in[4] <=  lane_in[4] + 8;
			lane_in[5] <=  lane_in[5] + 8;
			lane_in[6] <=  lane_in[6] + 8;
			lane_in[7] <=  lane_in[7] + 8;
		end
	end
endmodule

`endif

