//`define SIMULATION
module ROM
	#( parameter DATA_WIDTH = 32,
	parameter SIZE = 1024,
	parameter ADDR_WIDTH = $clog2(SIZE),
	parameter INITIALIZE = "initialize.mif"
	)
	(
	//------------------- input ---------------
	input clk,
	input read_en,
	input [ADDR_WIDTH - 1 : 0] read_addr,
	//------------------- output --------------
	output logic [DATA_WIDTH -1 : 0] read_data
	);

	logic [DATA_WIDTH - 1 : 0] data[SIZE];
	
	always_ff @(posedge clk)
	begin
		if(read_en)
			read_data <= data[read_addr];
		else
			read_data <={DATA_WIDTH{1'bx}};	
	end

	initial begin
		$readmemh(INITIALIZE,data);
		`ifdef SIMULATION
			for(int i =0;i<SIZE;i++)
				$display("%m,data[%d]=%d",i,data[i]);
		`endif
	end

endmodule
