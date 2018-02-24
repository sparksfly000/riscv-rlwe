#-------------------------------------------------------------------
#	
#	Filename			: makefile
#	Author        : Pang Yalong
#	Created       : 2017-3-15
#	Description   : makefile to use vcs
#   Targets		  :	make vcslog	compile with vcs
#					make vcsim	run simulation with vcs
#
#-------------------------------------------------------------------

#*** VARIABLES *****************************************************************

NAME_TOP			:= scr1_top_tb
USERNAME			:= $(shell whoami)
SOURCE_FILE    := file.list
TEST_INFO      :="./testcases/test_info"
TEST_RESULTS   :="./testcases/test_results.txt"
IMEM_PATTERN   :=FFFFFFFF
DMEM_PATTERN   :=FFFFFFFF

OUT_DIR=out
LOG_DIR=log

#*** MAIN BODY *****************************************************************

default:
	@echo 
	@echo "Make targets:"
	@echo "  make vcssim     run simulations using vcs"
	@echo "  make vcslog     compile modules only using vcs"
	@echo "  make dve        show the waveform"
	@echo 

# compile with vcs 
vcslog:
	mkdir -p $(LOG_DIR)
	vcs +v2k  -f  $(SOURCE_FILE) -full64 -sverilog -debug_pp +notimingcheck -timescale=1ns/10ps | tee $(LOG_DIR)/sim_pre.log

# run simulation with vcs
vcssim: vcslog
	mkdir -p $(OUT_DIR)
	./simv   +test_info=$(TEST_INFO) +test_results=$(TEST_RESULTS)  +imem_pattern=$(IMEM_PATTERN)  +dmem_pattern=$(DMEM_PATTERN) -ucli -do do.tcl |tee  $(LOG_DIR)/sim.log 
dve:
	dve -full64 -vpd inter.vpd
#clean 
clean:
	rm -rf $(LOG_DIR) $(OUT_DIR)  simv DVEfiles/  csrc/  simv.daidir/ ucli.key  inter.vpd 

