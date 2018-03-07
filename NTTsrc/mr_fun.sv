//@file : module reduce file

module mr_fun
	#(parameter U_WIDTH = 31,
	  parameter M       = 12289,
	  parameter M_WIDTH = $clog2(M),
	  parameter MIU     = 349496)  // 2^(n+alpha)/M   is a constant in design.
	(
//  input  port
	input clk,
	input rst_n,
	input logic [U_WIDTH - 1 : 0] U,
	input valid_in,

//  output port
	output logic [M_WIDTH - 1 : 0] Z,
	output logic valid_out

);

localparam MIU_WIDTH = $clog2(MIU);
localparam alpha = U_WIDTH - M_WIDTH + 1;


logic [U_WIDTH - M_WIDTH + 1 : 0] U_div;
logic [U_WIDTH - M_WIDTH     : 0] q_about,q_about_reg;   
logic [U_WIDTH - M_WIDTH + 1 + MIU_WIDTH : 0] product1;
logic [U_WIDTH - 1 : 0] product2,product2_reg;
logic [M_WIDTH  : 0] Z_about;
logic [U_WIDTH - 1 : 0] U_reg1,U_reg2;
logic vd_reg1,vd_reg2;

// the first pipeline stage
assign U_div = U >> (M_WIDTH - 2);
assign product1 = U_div * MIU;
assign q_about = product1 >> (alpha + 2);

always_ff @(posedge clk or negedge rst_n) begin : proc_
	if(~rst_n) begin
		q_about_reg <= 0;
		vd_reg1     <= 0;
		U_reg1      <= 0;
	end 
	else begin
		q_about_reg <= q_about ;
		vd_reg1     <= valid_in;
		U_reg1      <= U;
	end
end

// the second pipeline stage

assign product2 = q_about_reg * M;

always_ff @(posedge clk or negedge rst_n) begin 
	if(~rst_n) begin
		 product2_reg <= 0;
		 vd_reg2      <= 0;
		 U_reg2       <= 0;
	end else begin
		 product2_reg <= product2;
		 vd_reg2      <= vd_reg1 ;
		 U_reg2       <= U_reg1 ;
	end
end

// the third pipeline stage 


assign Z_about = U_reg2 - product2_reg;
always_ff @(posedge clk or negedge rst_n) begin 
	if(~rst_n) begin
		Z         <= 0;
		valid_out <= 0;
	end else begin
		valid_out = vd_reg2;
		if(Z_about > M)
			Z <= Z_about - M;
		else
			Z <= Z_about; 
	end
end

endmodule



// test

`ifdef TEST
module mr_fun_tb;

// parameter define
parameter U_WIDTH = 31;
parameter M       = 12289;
parameter M_WIDTH = $clog2(M);
parameter MIU     = 349496 ;

logic clk,rst_n,valid_in,valid_out;
logic [U_WIDTH - 1 : 0 ] U;
logic [M_WIDTH - 1 : 0 ] Z;



mr_fun #(.U_WIDTH (U_WIDTH),
		 .M       (M),
		 .M_WIDTH (M_WIDTH),
		 .MIU     (MIU))
		mr_fun_i(.*);

initial begin
	valid_in = 1'b1;
	rst_n <= 1'b1;
	clk = 1'b0;
forever begin
	U = (1<<U_WIDTH)-1;
	# 10;
	$display("U=%d,Z=%d",U,Z);
	assert(Z == U % mr_top_i.M);
end

end


always #5 clk = !clk;

endmodule
`endif