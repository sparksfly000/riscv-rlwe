module rlwecore
		#(parameter WIDTH = 32)
		(
		input 							 clk,
		input 							 rst_n,
	
		// FIFO Interface
    	input logic                 full,
    	input logic                 almost_full,
    	input logic                 empty,
    	input logic                 almost_empty,
    	output logic                dequeue_en,
    	input [WIDTH - 1:0]         value_o,

	 // rlwe core interface 
    input    logic                           rlwe_dmem_req_ack,
    output   logic                           rlwe_dmem_req,
    output   type_scr1_mem_cmd_e             rlwe_dmem_cmd,
    output   type_scr1_mem_width_e           rlwe_dmem_width,
    output   logic [`SCR1_DMEM_AWIDTH-1:0]   rlwe_dmem_addr,
    output   type_vector						   rlwe_dmem_wdata,
    input    type_vector						   rlwe_dmem_rdata,
    input    type_scr1_mem_resp_e            rlwe_dmem_resp
);		


//  assign rlwe_dmem_req = 1'b0;
//-----------------------------------------------
// move instr from FIFO to instr memory logic
//-----------------------------------------------
	localparam MAX_SIZE =1 * 1024 * 1024;
	localparam ADDR_WIDTH = $clog2(MAX_SIZE);
	logic [ADDR_WIDTH - 1 : 0] fifo_imem_addr;
	logic rlwe_start;	

   logic [`SCR1_IMEM_AWIDTH-1:0]           imem_addr;
   logic [`SCR1_IMEM_DWIDTH-1:0]           imem_rdata;
	logic                                   imem_req;
	always_ff@(posedge clk or negedge rst_n) 
	begin
		if(!rst_n) begin
			fifo_imem_addr 	<= '0;
			rlwe_start <= '0;
		end
		else
			if(!empty) begin
				fifo_imem_addr <= fifo_imem_addr + 4;   //align 4 bytes
				rlwe_start <= 1'b1;
			end
						
	end

	assign dequeue_en = !empty;


    sram_1r1w  #(	.DATA_WIDTH(WIDTH),
    					.SIZE(MAX_SIZE))
	 imem
    (             .clk(clk),
                  .read_en(imem_req),
                  .read_addr(imem_addr),
                  .read_data(imem_rdata),
                  .write_en(dequeue_en),
                  .write_addr(fifo_imem_addr),
                  .write_data(value_o));


//--------------------------------------------------------------------
//   the rlwe core
//--------------------------------------------------------------------

rlwe_core_top i_rlwecore_top(
    // Common
 /*   input   logic  */                                 .rst_n(rst_n),
 /*   input   logic   */                                .test_mode(),
 /*   input   logic   */                                .clk(clk),
/*    output  logic   */                                .rst_n_out(),

    // Fuses
  /*  input   logic [`SCR1_XLEN-1:0]  */                .fuse_mhartid('1),

    // IRQ
`ifdef SCR1_IPIC_EN
/*    input   logic [SCR1_IRQ_LINES_NUM-1:0] */         .irq_lines(),
`else
 /*   input   logic    */                               .ext_irq(1'b0),
`endif // SCR1_IPIC_EN 
  /*  input   logic      */                             .soft_irq(1'b0),

    // Memory-mapped external timer
  /*  input   logic        */                           .timer_irq(),
  /*  input   logic [63:0]   */                         .mtime_ext(),


    // Instruction Memory Interface
  /*  input   logic           */                        .imem_req_ack(rlwe_start | !empty),  // compare with the imem_req the rlwe_start latency is one cycle? so add the !empty,so if no !empty will read the first instr twice  
  /*  output  logic             */                      .imem_req(imem_req),
   /* output  type_scr1_mem_cmd_e */                    .imem_cmd(),
   /* output  logic [`SCR1_IMEM_AWIDTH-1:0] */          .imem_addr(imem_addr),
   /* input   logic [`SCR1_IMEM_DWIDTH-1:0]   */        .imem_rdata(imem_rdata),
   /* input   type_scr1_mem_resp_e          */          .imem_resp(SCR1_MEM_RESP_RDY_OK),

    // Data Memory Interface
 /*   input   logic                          */         .dmem_req_ack(rlwe_dmem_req_ack),
 /*   output  logic                         */          .dmem_req(rlwe_dmem_req),
 /*   output  type_scr1_mem_cmd_e          */           .dmem_cmd(rlwe_dmem_cmd),
 /*   output  type_scr1_mem_width_e          */         .dmem_width(rlwe_dmem_width),
 /*   output  logic [`SCR1_DMEM_AWIDTH-1:0]  */         .dmem_addr(rlwe_dmem_addr),
 /*   output  type_vector						   */         .dmem_wdata(rlwe_dmem_wdata),
 /*   input   type_vector						   */         .dmem_rdata(rlwe_dmem_rdata),
 /*   input   type_scr1_mem_resp_e           */         .dmem_resp(rlwe_dmem_resp)
);


endmodule
