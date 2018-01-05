module rlwecore
		#(parameter WIDTH = 64)
		(
		input 							 clk,
		input 							 rst_n,
	
		// FIFO Interface
    	input logic                 full,
    	input logic                 almost_full,
    	input logic                 empty,
    	input logic                 almost_empty,
    	output logic                dequeue_en,
    	input [WIDTH - 1:0]         value_o);		

//-----------------------------------------------
// move instr from FIFO to instr memory logic
//-----------------------------------------------
	localparam MAX_SIZE = 1024;
	localparam ADDR_WIDTH = $clog2(MAX_SIZE);
	logic [ADDR_WIDTH - 1 : 0] fifo_imem_addr;
		


	always_ff@(posedge clk or negedge rst_n) 
	begin
		if(!rst_n)
			fifo_imem_addr 	<= '0;
		else
			if(!empty) begin
				fifo_imem_addr <= fifo_imem_addr + 1;
			end
						
	end

	assign dequeue_en = !empty;


    sram_1r1w  #(	.DATA_WIDTH(WIDTH),
    					.SIZE(MAX_SIZE))
	 imem
    (             .clk(clk),
                  .read_en(),
                  .read_addr(),
                  .read_data(),
                  .write_en(dequeue_en),
                  .write_addr(fifo_imem_addr),
                  .write_data(value_o));

endmodule
