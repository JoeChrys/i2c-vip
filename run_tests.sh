# ##################################################
# Usefull Flags
# -gui
# -linedebug
# -timescale 1ps/1ps
# -s -input restore.tcl
# -clean
# ##################################################


xrun -f run.args -seed random +UVM_TESTNAME=i2c_delay_and_clock_stretch_test -l i2c_delay_and_clock_stretch_test.log +DUMPNAME="i2c_delay_and_clock_stretch_test.vcd" +VERBOSITY=UVM_LOW