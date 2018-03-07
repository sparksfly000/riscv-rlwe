`include "defines.sv"
module ButterFly(
	// ---------------- input --------------
	input clk,rst_n,
	input valid_in,
	input lane_t lane_in,
	input is_inv_ntt,
	// ---------------- output -------------
	output lane_t lane_out,
    output logic valid_out	
);
lane_t weigh[`R - 1 : 0 ];
data_t w1,w2,w3;

assign w1 = is_inv_ntt ? 5146 : 4043 ;
assign w2 = is_inv_ntt ? 10810 : 1479 ;
assign w3 =is_inv_ntt ? 8246 : 7143 ;

assign weigh[0][0]=1;
assign weigh[0][1]=1;
assign weigh[0][2]=1;
assign weigh[0][3]=1;
assign weigh[0][4]=1;
assign weigh[0][5]=1;
assign weigh[0][6]=1;
assign weigh[0][7]=1;

assign weigh[1][0]=1;
assign weigh[1][1]=w1;
assign weigh[1][2]=w2;
assign weigh[1][3]=w3;
assign weigh[1][4]=`M-1;
assign weigh[1][5]=`M-w1;
assign weigh[1][6]=`M-w2;
assign weigh[1][7]=`M-w3;


assign weigh[2][0]= 1;
assign weigh[2][1]= w2;
assign weigh[2][2]= `M-1;
assign weigh[2][3]= `M-w2;
assign weigh[2][4]= 1;
assign weigh[2][5]= w2;
assign weigh[2][6]= `M-1;
assign weigh[2][7]= `M-w2;


assign weigh[3][0]= 1;
assign weigh[3][1]= w3;
assign weigh[3][2]= `M-w2;
assign weigh[3][3]= w1;
assign weigh[3][4]= `M-1;
assign weigh[3][5]= `M-w3;
assign weigh[3][6]= w2;
assign weigh[3][7]= `M-w1;

assign weigh[4][0]= 1;
assign weigh[4][1]= `M-1;
assign weigh[4][2]= 1;
assign weigh[4][3]= `M-1;
assign weigh[4][4]= 1;
assign weigh[4][5]= `M-1;
assign weigh[4][6]= 1;
assign weigh[4][7]= `M-1;

assign weigh[5][0]= 1;
assign weigh[5][1]= `M-w1;
assign weigh[5][2]= w2;
assign weigh[5][3]= `M-w3;
assign weigh[5][4]= `M-1;
assign weigh[5][5]= w1;
assign weigh[5][6]= `M-w2;
assign weigh[5][7]= w3;

assign weigh[6][0]= 1;
assign weigh[6][1]= `M-w2;
assign weigh[6][2]= `M-1;
assign weigh[6][3]= w2;
assign weigh[6][4]= 1;
assign weigh[6][5]= `M-w2;
assign weigh[6][6]= `M-1;
assign weigh[6][7]= w2;

assign weigh[7][0]= 1;
assign weigh[7][1]= `M-w3;
assign weigh[7][2]= `M-w2;
assign weigh[7][3]= `M-w1;
assign weigh[7][4]= `M-1;
assign weigh[7][5]= w3;
assign weigh[7][6]= w2;
assign weigh[7][7]= w1;


`ifdef SIMULATION_VERSION
function data_t  butterfly;
input lane_t a;
input lane_t b;
begin
logic [34 : 0] mac;
mac =  a[0]*b[0] + a[1]*b[1] +a[2]*b[2] + a[3]*b[3] +a[4]*b[4] + a[5]*b[5] +a[6]*b[6] +a[7]*b[7];	
return mac %`M;	
end	
endfunction

genvar j;
generate for(j=0; j< `R; j++) begin :loop
	always_ff @(posedge clk)
		lane_out[j] <= butterfly(weigh[j], lane_in);
end
endgenerate

always_ff @(posedge clk)
begin
	valid_out <= valid_in;
end

`else 

logic vd_reg[4 : 1];

// first pipeline stage
logic [`R - 1 : 0][2 * $clog2(`M) - 1 : 0] product[`R];
logic [`R - 1 : 0][2 * $clog2(`M) - 1 : 0] product_reg[`R];

genvar  j;
generate for(j=0; j<`R; j++) begin :loop
	assign product[j][0] = weigh[j][0] * lane_in[0];
	assign product[j][1] = weigh[j][1] * lane_in[1];
	assign product[j][2] = weigh[j][2] * lane_in[2];
	assign product[j][3] = weigh[j][3] * lane_in[3];
	assign product[j][4] = weigh[j][4] * lane_in[4];
	assign product[j][5] = weigh[j][5] * lane_in[5];
	assign product[j][6] = weigh[j][6] * lane_in[6];
	assign product[j][7] = weigh[j][7] * lane_in[7];
end
endgenerate

always_ff @(posedge clk or negedge rst_n) begin 
	if(~rst_n) begin
		product_reg [0]<= 0;
		product_reg [1]<= 0;
		product_reg [2]<= 0;
		product_reg [3]<= 0;
		product_reg [4]<= 0;
		product_reg [5]<= 0;
		product_reg [6]<= 0;
		product_reg [7]<= 0;
		vd_reg[1]      <= 0;
	end else begin
		product_reg <= product;
		vd_reg[1]   <= valid_in;
	end
end


// second pipeline stage

logic [`R/2 - 1 : 0][2 * $clog2(`M) : 0] sum_second[`R];
logic [`R/2 - 1 : 0][2 * $clog2(`M) : 0] sum_second_reg[`R];
generate for(j=0; j <`R; j++) begin : sum_second_loop
	assign sum_second[j][0] = product_reg[j][0] + product_reg[j][1];
	assign sum_second[j][1] = product_reg[j][2] + product_reg[j][3];
	assign sum_second[j][2] = product_reg[j][4] + product_reg[j][5];
	assign sum_second[j][3] = product_reg[j][6] + product_reg[j][7];
end
endgenerate
always_ff @(posedge clk or negedge rst_n) begin 
	if(~rst_n) begin
		sum_second_reg[0] <= 0;
		sum_second_reg[1] <= 0;
		sum_second_reg[2] <= 0;
		sum_second_reg[3] <= 0;
		sum_second_reg[4] <= 0;
		sum_second_reg[5] <= 0;
		sum_second_reg[6] <= 0;
		sum_second_reg[7] <= 0;
		vd_reg[2]         <= 0;
	end else begin
		sum_second_reg <= sum_second;
		vd_reg[2]      <= vd_reg[1];
	end
end

// third pipeline stage
logic [`R/4 - 1 : 0][2 * $clog2(`M) + 1: 0] sum_third[`R];
logic [`R/4 - 1 : 0][2 * $clog2(`M) + 1: 0] sum_third_reg[`R];
generate for(j=0; j<`R; j++) begin : sum_third_loop
	assign sum_third[j][0] = sum_second_reg[j][0] + sum_second_reg[j][1];
	assign sum_third[j][1] = sum_second_reg[j][2] + sum_second_reg[j][3];
end
endgenerate
always_ff @(posedge clk or negedge rst_n) begin 
	if(~rst_n) begin
		sum_third_reg[0] <= 0;
		sum_third_reg[1] <= 0;
		sum_third_reg[2] <= 0;
		sum_third_reg[3] <= 0;
		sum_third_reg[4] <= 0;
		sum_third_reg[5] <= 0;
		sum_third_reg[6] <= 0;
		sum_third_reg[7] <= 0;
		vd_reg[3]     <= 0;
	end else begin
		sum_third_reg <= sum_third;
		vd_reg[3]     <= vd_reg[2] ;
	end
end

//forth pipeline stage
logic [2 * $clog2(`M) + 2: 0] sum_forth[`R];
logic [2 * $clog2(`M) + 2: 0] sum_forth_reg[`R];
generate for(j=0; j<`R; j++) begin : sum_forth_loop
	assign sum_forth[j] = sum_third_reg[j][0] + sum_third_reg[j][1];
	
end
endgenerate
always_ff @(posedge clk or negedge rst_n) begin 
	if(~rst_n) begin
		sum_forth_reg[0] <= 0;
		sum_forth_reg[1] <= 0;
		sum_forth_reg[2] <= 0;
		sum_forth_reg[3] <= 0;
		sum_forth_reg[4] <= 0;
		sum_forth_reg[5] <= 0;
		sum_forth_reg[6] <= 0;
		sum_forth_reg[7] <= 0;
		vd_reg[4]        <= 0;
	end else begin
		sum_forth_reg <= sum_forth;
		vd_reg[4]     <= vd_reg[3];
	end
end

// the modulo reduce logic

logic mr_valid[`R];
generate for(j= 0; j< `R; j++) begin : mr_loop
mr_fun #(.U_WIDTH (2 * $clog2(`M) + 3),
		 .M       (`M),
		 .MIU     (`MIU))
		mr_fun_i(
		.clk      (clk),
		.rst_n    (rst_n),
		.valid_in (vd_reg[4]),
		.U        (sum_forth_reg[j]),
		.valid_out(mr_valid[j]),
		.Z        (lane_out[j]));
end
endgenerate

assign valid_out = mr_valid[0];

`endif
endmodule



/*
//----------------------- testbench ------------------
module butterfly_tb;

	logic clk,rst_n;
	lane_t in;
	lane_t result;
	ButterFly ButterFly(.*);
       	initial
	begin
	for(int i=0; i<`R; i++)
		in[i]={$random}%`M;
	end	
endmodule
*/
