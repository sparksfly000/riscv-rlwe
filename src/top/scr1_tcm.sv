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
    output  logic                           core_dmem_req_ack,
    input   logic                           core_dmem_req,
    input   type_scr1_mem_cmd_e             core_dmem_cmd,
    input   type_scr1_mem_width_e           core_dmem_width,
    input   logic [`SCR1_DMEM_AWIDTH-1:0]   core_dmem_addr,
    input   type_vector						     core_dmem_wdata,
    output  type_vector						     core_dmem_rdata,
    output  type_scr1_mem_resp_e            core_dmem_resp,
    
    // rlwe interface
	 output  logic                           rlwe_dmem_req_ack,
    input   logic                           rlwe_dmem_req,
    input   type_scr1_mem_cmd_e             rlwe_dmem_cmd,
    input   type_scr1_mem_width_e           rlwe_dmem_width,
    input   logic [`SCR1_DMEM_AWIDTH-1:0]   rlwe_dmem_addr,
    input   type_vector						     rlwe_dmem_wdata,
    output  type_vector						     rlwe_dmem_rdata,
    output  type_scr1_mem_resp_e            rlwe_dmem_resp
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_FSM_ADDR,
    SCR1_FSM_DATA
} type_scr1_fsm_e;

typedef enum logic {
    SCR1_SEL_CORE,
    SCR1_SEL_RLWE
} type_core_sel_e;


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
type_scr1_fsm_e                     fsm;
type_core_sel_e                     core_sel;
type_core_sel_e                     core_sel_r;
type_scr1_mem_cmd_e                 dmem_cmd;
type_scr1_mem_width_e               dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]       dmem_addr;
type_vector						         dmem_wdata;
type_scr1_mem_resp_e                dmem_resp;
type_vector						         dmem_rdata;
logic                               sel_req_ack;


//-------------------------------------------------------------------------------
// core or rlwe select logic
//-------------------------------------------------------------------------------
assign dmem_req = core_dmem_req | rlwe_dmem_req;

always_comb begin
	core_sel = SCR1_SEL_CORE;
	if (core_dmem_req)                       // the core has the higher priority
		core_sel = SCR1_SEL_CORE;
	else if(rlwe_dmem_req)
		core_sel = SCR1_SEL_RLWE;
end

assign dmem_cmd =(core_sel == SCR1_SEL_CORE) ? core_dmem_cmd : rlwe_dmem_cmd;
assign dmem_width =(core_sel == SCR1_SEL_CORE) ? core_dmem_width : rlwe_dmem_width;
assign dmem_addr =(core_sel == SCR1_SEL_CORE) ? core_dmem_addr : rlwe_dmem_addr;
assign dmem_wdata =(core_sel == SCR1_SEL_CORE) ? core_dmem_wdata : rlwe_dmem_wdata;


// FSM
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        fsm         <= SCR1_FSM_ADDR;
		  core_sel_r  <= SCR1_SEL_CORE;
    end else begin
        case (fsm)
            SCR1_FSM_ADDR : begin
                if (dmem_req & sel_req_ack) begin
                    fsm         <= SCR1_FSM_DATA;
						  core_sel_r  <= core_sel;
                end
            end
            SCR1_FSM_DATA : begin
                case (dmem_resp)
                    SCR1_MEM_RESP_RDY_OK : begin
                        if (dmem_req & sel_req_ack) begin
                            fsm         <= SCR1_FSM_DATA;
									 core_sel_r  <= core_sel;
                        end else begin
                            fsm <= SCR1_FSM_ADDR;
                        end
                    end
                    SCR1_MEM_RESP_RDY_ER : begin
                        fsm <= SCR1_FSM_ADDR;
                    end
                    default : begin
                    end
                endcase
            end
            default : begin
            end
        endcase
    end
end

//-------------------------------------------------------------------------------
// Interface to core
//-------------------------------------------------------------------------------


always_comb begin
    case (core_sel_r)
        SCR1_SEL_CORE  : begin
				core_dmem_rdata   = dmem_rdata; 
            core_dmem_resp    = dmem_resp;
        end
        SCR1_SEL_RLWE  : begin
				core_dmem_rdata   = '0; 
            core_dmem_resp    = SCR1_MEM_RESP_NOTRDY;
        end
        default         : begin
				core_dmem_rdata   = '0;
				core_dmem_resp    = SCR1_MEM_RESP_NOTRDY;
        end
    endcase
end


//-------------------------------------------------------------------------------
// Interface to rlwe core
//-------------------------------------------------------------------------------


always_comb begin
    case (core_sel_r)
        SCR1_SEL_CORE  : begin
				rlwe_dmem_rdata   = '0; 
            rlwe_dmem_resp    = SCR1_MEM_RESP_NOTRDY;
        end
        SCR1_SEL_RLWE  : begin
				rlwe_dmem_rdata   = dmem_rdata; 
            rlwe_dmem_resp    = dmem_resp;
        end
        default         : begin
				rlwe_dmem_rdata   = '0;
				rlwe_dmem_resp    = SCR1_MEM_RESP_NOTRDY;
        end
    endcase
end




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
assign core_dmem_req_ack = 1'b1;
assign rlwe_dmem_req_ack = 1'b1;
assign sel_req_ack = 1'b1;
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
    .rst_n  (rst_n											 ),
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
