`include "defines.sv"
module controller(
	// --------------------- input --------------------
	input clk,rst_n,
	// --------------------- output -------------------
	output [`L - 1 : 0] BF_en,
	output [`L - 1 : 0] COM_en,
	output address_t twiddle0,
	output address_t twiddle1
);

logic [$clog2(`N)  : 0] counter;
logic [$clog2(`N/`R) - 1 : 0] counter_twiddle0;
logic [$clog2(`N/`R/`R) -1 : 0] counter_twiddle1;

always@(posedge clk or negedge rst_n)
begin
	if(!rst_n)
		counter <= 0;
	else 
		counter <= counter + 1'b1;
end

always @(posedge clk or negedge rst_n)
begin
	if(!rst_n)
		counter_twiddle0 <= 0;
	else if(BF_en[0])
		counter_twiddle0 <= counter_twiddle0 + 1'b1;
end

always @(posedge clk or negedge rst_n)
begin
	if(!rst_n)
		counter_twiddle1 <= 0;
	else if(BF_en[1])
		counter_twiddle1 <= counter_twiddle1 + 1'b1;
end

genvar index;
generate for(index = 1; index < `R; index++) begin:twiddle_gen
	assign twiddle0[index] = index * counter_twiddle0;
	assign twiddle1[index] = index * counter_twiddle1 * `R;
end
endgenerate
assign BF_en[0] = ( counter > `DELAY0MAX - 1);
assign BF_en[1] = ( counter > 508 - 1);
assign BF_en[2] = (counter > 519 - 1);



endmodule

/*
// ---------------------- testbench -------------------------

module controller_tb;
logic clk,rst_n;
logic [`L - 1: 0] BF_en,COM_en;
address_t twiddle0,twiddle1;

controller controller(.*);
initial begin
clk=1'b0;
rst_n = 1'b0;
#10;
rst_n = 1'b1;

end


always begin
#5;
clk=!clk;
end

endmodule
*/
