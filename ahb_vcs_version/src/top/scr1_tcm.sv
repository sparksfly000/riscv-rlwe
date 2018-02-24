/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_tcm.sv>
/// @brief      Tightly-coupled memory (TCM)
///
`include "scr1_memif.svh"
`include "scr1_arch_description.svh"
`include "defines.svh"

module scr1_tcm
#(
    parameter SCR1_TCM_SIZE = `SCR1_IMEM_AWIDTH'h00010000
)
(
    // Control signals
    input   logic                           clk,
    input   logic                           rst_n,

    // Core instruction interface
    output  logic                           imem_req_ack,
    input   logic                           imem_req,
    input   type_scr1_mem_cmd_e             imem_cmd,
    input   logic [`SCR1_IMEM_AWIDTH-1:0]   imem_addr,
    output  logic [`SCR1_IMEM_DWIDTH-1:0]   imem_rdata,
    output  type_scr1_mem_resp_e            imem_resp,

    // Core data interface
    output  logic                           dmem_req_ack,
    input   logic                           dmem_req,
    input   type_scr1_mem_cmd_e             dmem_cmd,
    input   type_scr1_mem_width_e           dmem_width,
    input   logic [`SCR1_DMEM_AWIDTH-1:0]   dmem_addr,
    input   type_vector						     dmem_wdata,
    output  type_vector						     dmem_rdata,
    output  type_scr1_mem_resp_e            dmem_resp
);

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic                               imem_req_en;
logic                               dmem_req_en;
logic                               imem_rd;
logic                               dmem_rd;
logic                               dmem_wr;
type_vector						         dmem_writedata;
type_vector						         dmem_rdata_local;
logic [3:0]                         dmem_byteen;
logic [1:0]                         dmem_rdata_shift_reg;
logic                               w_is_vector;
//-------------------------------------------------------------------------------
// Core interface
//-------------------------------------------------------------------------------
assign imem_req_en = (imem_resp == SCR1_MEM_RESP_RDY_OK) ^ imem_req;
assign dmem_req_en = (dmem_resp == SCR1_MEM_RESP_RDY_OK) ^ dmem_req;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        imem_resp <= SCR1_MEM_RESP_NOTRDY;
    end else if (imem_req_en) begin
        imem_resp <= imem_req ? SCR1_MEM_RESP_RDY_OK : SCR1_MEM_RESP_NOTRDY;
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dmem_resp <= SCR1_MEM_RESP_NOTRDY;
    end else if (dmem_req_en) begin
        dmem_resp <= dmem_req ? SCR1_MEM_RESP_RDY_OK : SCR1_MEM_RESP_NOTRDY;
    end
end

assign imem_req_ack = 1'b1;
assign dmem_req_ack = 1'b1;
//-------------------------------------------------------------------------------
// Memory data composing
//-------------------------------------------------------------------------------
assign imem_rd  = 1'b1;
assign dmem_rd  = 1'b1;
assign dmem_wr  = dmem_req & (dmem_cmd == SCR1_MEM_CMD_WR);

always_comb begin
    dmem_writedata = dmem_wdata;
    dmem_byteen    = 4'b1111;
	 w_is_vector    = 1'b1;
    case ( dmem_width )
        SCR1_MEM_WIDTH_BYTE : begin
            dmem_writedata  = {(`LANE*`SCR1_DMEM_DWIDTH /  8){dmem_wdata[0][7:0]}};
            dmem_byteen     = 1'b1 << dmem_addr[1:0];
	 			w_is_vector     = 1'b0;
        end
        SCR1_MEM_WIDTH_HWORD : begin
            dmem_writedata  = {(`LANE*`SCR1_DMEM_DWIDTH / 16){dmem_wdata[0][15:0]}};
            dmem_byteen     = 2'b11 << {dmem_addr[1], 1'b0};
	 			w_is_vector     = 1'b0;
        end
        SCR1_MEM_WIDTH_WORD : begin
            dmem_writedata  = {(`LANE*`SCR1_DMEM_DWIDTH / 32){dmem_wdata[0][31:0]}};
            dmem_byteen     = 4'b1111;
	 			w_is_vector     = 1'b0;
        end
        default : begin
        end
    endcase
end
//-------------------------------------------------------------------------------
// Memory instantiation
//-------------------------------------------------------------------------------
scr1_dp_memory #(
    .SCR1_WIDTH ( 32            ),
    .SCR1_SIZE  ( SCR1_TCM_SIZE )
) i_dp_memory (
    .clk    ( clk                                   ),
    // Instruction port
    // Port A
    .rena   ( imem_rd                               ),
    .addra  ( imem_addr[$clog2(SCR1_TCM_SIZE)-1:2]  ),
    .qa     ( imem_rdata                            ),
    // Data port
    // Port B
    .renb   ( dmem_rd                               ),
    .wenb   ( dmem_wr                               ),
    .webb   ( dmem_byteen                           ),
	 .w_is_vector(w_is_vector                        ),
    .addrb  ( dmem_addr[$clog2(SCR1_TCM_SIZE)-1:2]  ),
    .qb     ( dmem_rdata_local                      ),
    .datab  ( dmem_writedata                        )
);
//-------------------------------------------------------------------------------
// Data memory output generation
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (dmem_rd) begin
        dmem_rdata_shift_reg <= dmem_addr[1:0];
    end
end

assign dmem_rdata[0] = dmem_rdata_local[0] >> ( 8 * dmem_rdata_shift_reg );
assign dmem_rdata[`LANE - 1:1] = dmem_rdata_local[`LANE - 1:1];

endmodule : scr1_tcm
