#!/bin/tcsh

# Array of test names
set TESTNAMES = (i2c_delay_and_clock_stretch_test)

# Number of times to run each test
set N = 1

# Iterate over test names
foreach TESTNAME ($TESTNAMES)
    # Inner loop to run each test N times
    foreach i (`seq 1 $N`)
        # Run the command with the current test name and seed
        echo "\n\nRunning test: $TESTNAME, seed: $i\n\n"
        xrun -f run.args -seed $i -coverage all +VERBOSITY=UVM_NONE +UVM_TESTNAME=$TESTNAME -l logs/${TESTNAME}_$i.log +DUMPNAME="${TESTNAME}_$i.vcd" -covtest ${TESTNAME}_$i
    end
end
