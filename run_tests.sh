# ##################################################
# Usefull Flags
# -gui
# -LINEDEBUG
# -timescale 1ps/1ps
# -s -input restore.tcl
# ##################################################

# xrun top.sv -timescale 1ns/1ns -sysv -access +rw -uvm -seed random -uvmhome CDNS-1.2 +UVM_TESTNAME=temp_rst_test -clean -l temp_rst_test.log +DUMPNAME="temp_rst_test.vcd" +VERBOSITY=UVM_LOW
# xrun top.sv -timescale 1ns/1ns -sysv -access +rw -uvm -seed random -uvmhome CDNS-1.2 +UVM_TESTNAME=i2c_random_test -clean -l i2c_random_test.log +DUMPNAME="i2c_random_test.vcd" +VERBOSITY=UVM_DEBUG -gui
# xrun top.sv -timescale 1ns/1ns -sysv -access +rw -uvm -seed 1 -uvmhome CDNS-1.2 +UVM_TESTNAME=i2c_testing_test -clean -l i2c_random_test.log +DUMPNAME="i2c_random_test.vcd" +VERBOSITY=UVM_LOW -gui
# xrun top.sv -timescale 1ns/1ns -sysv -access +rw -uvm -seed 1 -uvmhome CDNS-1.2 +UVM_TESTNAME=i2c_testing_test -clean -l i2c_random_test.log +DUMPNAME=i2c_random_test.vcd +VERBOSITY=UVM_LOW -s -input restore.tcl
# xrun src/top.sv -incdir "src/" -incdir "src/agents" -incdir "src/env" -incdir "src/tests" -s -input restore.tcl -sysv -access +rw -uvm -uvmhome CDNS-1.2 -clean -l i2c_testing_test.log -seed 1 -timescale 1ns/1ns +UVM_TESTNAME=i2c_testing_test +DUMPNAME="i2c_testing_test.vcd" +VERBOSITY=UVM_LOW
# xrun src/top.sv -incdir "src/" -incdir "src/agents" -incdir "src/env" -incdir "src/tests" -s -input restore.tcl -sysv -access +rw -uvm -uvmhome CDNS-1.2 -clean -l i2c_basic_test.log -seed 1 -timescale 1ns/1ns +UVM_TESTNAME=i2c_basic_test +DUMPNAME="i2c_basic_test.vcd" +VERBOSITY=UVM_LOW
xrun -f run.args +UVM_TESTNAME=i2c_delay_and_clock_stretch_test