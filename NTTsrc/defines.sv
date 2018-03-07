`ifndef DEFINES_SV_
`define DEFINES_SV_

`define N 512
`define N_inv 12265
`define R 8
`define M 12289
`define MIU 349496     // 2^32%M
`define DATA_GAP 2
`define L $clog2(`N)/$clog2(`R)
`define DELAY0MAX  `N/`R*(`R-1)
`define MR_DELAY 3
typedef logic [$clog2(`N)-1 : 0] width_t;
typedef logic [32 - 1 : 0] data_t;
typedef width_t [`R - 1 : 1] address_t;
typedef data_t [`R - 1 : 0] lane_t; 

typedef enum logic [1:0] {
	PAIRWISE_MUL,
	PAIRWISE_ADD,
	PAIRWISE_SUB,
	PAIRWISE_NONE
}type_pairwise_op_e;

`endif
