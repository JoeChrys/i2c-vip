# ##################################################
# Usefull Flags
# -gui
# -LINEDEBUG
# -timescale 1ps/1ps
# -s -input restore.tcl
# ##################################################

# xrun top.sv -timescale 1ns/1ns -sysv -access +rw -uvm -seed random -uvmhome CDNS-1.2 +UVM_TESTNAME=temp_rst_test -clean -l temp_rst_test.log +DUMPNAME="temp_rst_test.vcd" +VERBOSITY=UVM_LOW
# xrun top.sv -timescale 1ns/1ns -sysv -access +rw -uvm -seed random -uvmhome CDNS-1.2 +UVM_TESTNAME=i2c_random_test -clean -l i2c_random_test.log +DUMPNAME="i2c_random_test.vcd" +VERBOSITY=UVM_DEBUG -gui
xrun top.sv -timescale 1ps/1ps -sysv -access +rw -uvm -seed 1 -uvmhome CDNS-1.2 +UVM_TESTNAME=i2c_testing_test -clean -l i2c_random_test.log +DUMPNAME="i2c_random_test.vcd" +VERBOSITY=UVM_DEBUG -s -input restore.tcl -gui
