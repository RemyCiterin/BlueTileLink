RTL = rtl
BUILD = build
BSIM = bsim
PACKAGES = ./src/:+
SIM_FILE = ./build/mkTop_sim
TOP = src/Soc.bsv

BSIM_MODULE = mkCPU_SIM

BUILD_MODULE = mkCPU


LIB = \
			$(BLUESPECDIR)/Verilog/SizedFIFO.v \
			$(BLUESPECDIR)/Verilog/SizedFIFO0.v \
			$(BLUESPECDIR)/Verilog/FIFO1.v \
			$(BLUESPECDIR)/Verilog/FIFO2.v \
			$(BLUESPECDIR)/Verilog/FIFO20.v \
			$(BLUESPECDIR)/Verilog/FIFO10.v \
			$(BLUESPECDIR)/Verilog/BRAM1.v \
			$(BLUESPECDIR)/Verilog/BRAM1BELoad.v \
			$(BLUESPECDIR)/Verilog/BRAM2.v \
			$(BLUESPECDIR)/Verilog/RevertReg.v \
			$(BLUESPECDIR)/Verilog/RegFile.v \
			$(BLUESPECDIR)/Verilog/RegFileLoad.v

BSC_FLAGS = -show-schedule -show-range-conflict -keep-fires -aggressive-conditions \
						-check-assert -no-warn-action-shadowing -sched-dot

SYNTH_FLAGS = -bdir $(BUILD) -vdir $(RTL) -simdir $(BUILD) \
							-info-dir $(BUILD) -fdir $(BUILD) #-D BSIM

BSIM_FLAGS = -bdir $(BSIM) -vdir $(BSIM) -simdir $(BSIM) \
							-info-dir $(BSIM) -fdir $(BSIM) -D BSIM -l pthread

compile:
	bsc \
		$(SYNTH_FLAGS) $(BSC_FLAGS) -cpp +RTS -K128M -RTS \
		-p $(PACKAGES) -verilog -u -g $(BUILD_MODULE) $(TOP)

sim:
	bsc $(BSC_FLAGS) $(BSIM_FLAGS) -p $(PACKAGES) -sim -u -g $(BSIM_MODULE) $(TOP)
	bsc $(BSC_FLAGS) $(BSIM_FLAGS) -sim -e $(BSIM_MODULE) -o \
		$(BSIM)/bsim $(BSIM)/*.ba
	./bsim/bsim -m 1000000000

run:
	./bsim/bsim -m 1000000000

clean:
	rm -rf $(BUILD)/*
	rm -rf $(BSIM)/*
	rm -rf $(RTL)/*
