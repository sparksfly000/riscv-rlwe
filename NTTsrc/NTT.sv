`include "defines.sv"
module NTT(
	//-----------------intput -------------------------
	input clk,rst_n,valid_in,
	input lane_t lane_in,
	input is_inv_ntt,
	//-----------------output -------------------------
	output lane_t lane_out,
	output logic valid_out,
	output logic nttend
);


logic valid_delay[ 14: 0];
lane_t lane_delay[14:0];
input_commutor input_commutor(.lane_out(lane_delay[0]),.valid_out(valid_delay[0]),.*);
ButterFly ButterFly1(.valid_in(valid_delay[0]),.lane_in(lane_delay[0]),.valid_out(valid_delay[1]),.lane_out(lane_delay[1]),.*);
TwiddleFactor #(.DATA_WIDTH($clog2(`M)),.SIZE(64))TwiddleFactor(.valid_in(valid_delay[1]),.lane_in(lane_delay[1]),.valid_out(valid_delay[2]),.lane_out(lane_delay[2]),.*);
delay_unit #(0,8,16,24,32,40,48,56) delay_unit0(.valid_in(valid_delay[2]),.lane_in(lane_delay[2]),.valid_out(valid_delay[3]),.lane_out(lane_delay[3]),.extend(1'b1),.*);
commutor0 commutor0(.valid_in(valid_delay[3]),.lane_in(lane_delay[3]),.valid_out(valid_delay[4]),.lane_out(lane_delay[4]),.*);
delay_unit #(56,48,40,32,24,16,8,0) delay_unit1(.valid_in(valid_delay[4]),.lane_in(lane_delay[4]),.valid_out(valid_delay[5]),.lane_out(lane_delay[5]),.extend(1'b0),.*);
ButterFly ButterFly2(.valid_in(valid_delay[5]),.lane_in(lane_delay[5]),.valid_out(valid_delay[6]),.lane_out(lane_delay[6]),.*);
TwiddleFactor2 #(.DATA_WIDTH($clog2(`M)),.SIZE(8))TwiddleFactor1(.valid_in(valid_delay[6]),.lane_in(lane_delay[6]),.valid_out(valid_delay[7]),.lane_out(lane_delay[7]),.*);
delay_unit #(0,1,2,3,4,5,6,7) delay_unit2(.valid_in(valid_delay[7]),.lane_in(lane_delay[7]),.valid_out(valid_delay[8]),.lane_out(lane_delay[8]),.extend(1'b1),.*);
commutor1 commutor1(.valid_in(valid_delay[8]),.lane_in(lane_delay[8]),.valid_out(valid_delay[9]),.lane_out(lane_delay[9]),.*);
delay_unit #(7,6,5,4,3,2,1,0) delay_unit3(.valid_in(valid_delay[9]),.lane_in(lane_delay[9]),.valid_out(valid_delay[10]),.lane_out(lane_delay[10]),.extend(1'b0),.*);
ButterFly ButterFly3(.valid_in(valid_delay[10]),.lane_in(lane_delay[10]),.valid_out(valid_delay[11]),.lane_out(lane_delay[11]),.*);
delay_unit #(0,8,16,24,32,40,48,56) delay_unit4(.valid_in(valid_delay[11]),.lane_in(lane_delay[11]),.valid_out(valid_delay[12]),.lane_out(lane_delay[12]),.extend(1'b1),.*);
commutor0 commutor0_0(.valid_in(valid_delay[12]),.lane_in(lane_delay[12]),.valid_out(valid_delay[13]),.lane_out(lane_delay[13]),.*);
delay_unit #(56,48,40,32,24,16,8,0) delay_unit5(.valid_in(valid_delay[13]),.lane_in(lane_delay[13]),.valid_out(valid_delay[14]),.lane_out(lane_delay[14]),.extend(1'b0),.*);
assign valid_out = valid_delay[14];
assign lane_out = lane_delay[14];

// the operation end signal
 
logic [7: 0]count;

always_ff@(posedge clk or negedge rst_n) begin
	if(!rst_n)
			count <= '0;
	else if(valid_out)
			count <= count + 1'b1;
	if(count == 64)
			count <= '0;
end

assign nttend = count == 64;

endmodule


`ifdef TESTNTT

// ----------------------------------- testbench --------------------------
module NTT_tb;

	logic clk,rst_n,valid_in,is_inv_ntt;
	lane_t lane_in;
	lane_t lane_out;
	logic valid_out;
    logic nttend;

	data_t data[`N -1 : 0];

	int file;
	initial begin
	is_inv_ntt = 1'b1;
	$readmemh("input.txt",data);
  	file= $fopen("result.txt","wb");
	clk= 1'b0;
	rst_n = 1'b0;
	#10;
	rst_n = 1'b1;
	# (3020*3);
	$fclose(file);
   $finish;
	end

initial begin
	 repeat(64) begin
		valid_in = 1'b0;
		#16;
		valid_in = 1'b1;
		#10;
		valid_in = 1'b0;
		#4;
	 end
	end

	
	logic valid_in_delay;
	always_ff@(posedge clk or negedge rst_n) begin
		if(!rst_n)
			valid_in_delay <= '0;
		else
			valid_in_delay <= valid_in;
	end

	NTT NTT(.valid_in(valid_in_delay),.*);

	logic [6:0] count;
	always_ff@(posedge clk or negedge rst_n)
	begin
		if(!rst_n) begin
			count <=0;
			lane_in <= '0;
		end else if(valid_in && count < 64)
		begin
			count <=count + 1'b1;
			lane_in[0] <= data[8*count];
			lane_in[1] <= data[8*count+1];
			lane_in[2] <= data[8*count+2];
			lane_in[3] <= data[8*count+3];
			lane_in[4] <= data[8*count+4];
			lane_in[5] <= data[8*count+5];
			lane_in[6] <= data[8*count+6];
			lane_in[7] <= data[8*count+7];
		end
		else begin
			for(int i=0; i<8;i++)
				lane_in[i] <={$clog2(`M){1'bx}};
		end
		end


	
	logic [6:0] count_out;
	always_ff@(posedge clk)
	begin
		if(!rst_n)
			count_out <=0;
		else if(valid_out && count_out < 64)
		begin
			count_out <=count_out + 1'b1;
			$fdisplay(file,"%h",lane_out[0]*1%`M);
			$fdisplay(file,"%h",lane_out[1]*1%`M);
			$fdisplay(file,"%h",lane_out[2]*1%`M);
			$fdisplay(file,"%h",lane_out[3]*1%`M);
			$fdisplay(file,"%h",lane_out[4]*1%`M);
			$fdisplay(file,"%h",lane_out[5]*1%`M);
			$fdisplay(file,"%h",lane_out[6]*1%`M);
			$fdisplay(file,"%h",lane_out[7]*1%`M);
		end
		end
	
	always begin
	#5;
	clk = !clk;
	end
endmodule 

`endif
