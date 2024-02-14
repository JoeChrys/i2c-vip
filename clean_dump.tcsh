#!/bin/tcsh

# Delete all .history files
foreach file (*.history)
    rm -f "$file"
end

# Delete all .vcd files
foreach file (*.vcd)
    rm -f "$file"
end