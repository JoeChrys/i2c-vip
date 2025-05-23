
# XM-Sim Command File
# TOOL:	xmsim(64)	22.03-s002
#
#
# You can restore this configuration with:
#
#      xrun src/top.sv -incdir src/ -incdir src/agents -incdir src/env -incdir src/tests -s -sysv -access +rw -uvm -uvmhome CDNS-1.2 -clean -l i2c_basic_test.log -seed 1 -timescale 1ns/1ns +UVM_TESTNAME=i2c_basic_test +DUMPNAME=i2c_basic_test.vcd +VERBOSITY=UVM_LOW -input restore.tcl
#

set tcl_prompt1 {puts -nonewline "xcelium> "}
set tcl_prompt2 {puts -nonewline "> "}
set vlog_format %h
set vhdl_format %v
set real_precision 6
set display_unit auto
set time_unit module
set heap_garbage_size -200
set heap_garbage_time 0
set assert_report_level note
set assert_stop_level error
set autoscope yes
set assert_1164_warnings yes
set pack_assert_off {}
set severity_pack_assert_off {note warning}
set assert_output_stop_level failed
set tcl_debug_level 0
set relax_path_name 1
set vhdl_vcdmap XX01ZX01X
set intovf_severity_level ERROR
set probe_screen_format 0
set rangecnst_severity_level ERROR
set textio_severity_level ERROR
set vital_timing_checks_on 1
set vlog_code_show_force 0
set assert_count_attempts 1
set tcl_all64 false
set tcl_runerror_exit false
set assert_report_incompletes 0
set show_force 1
set force_reset_by_reinvoke 0
set tcl_relaxed_literal 0
set probe_exclude_patterns {}
set probe_packed_limit 4k
set probe_unpacked_limit 16k
set assert_internal_msg no
set svseed 1
set assert_reporting_mode 0
set vcd_compact_mode 0
alias . run
alias quit exit
stop -create -name Randomize -randomize
database -open -vcd -into i2c_basic_test.vcd _i2c_basic_test.vcd1 -timescale fs
database -open -vcd -into i2c_random_test.vcd _i2c_random_test.vcd1 -timescale fs
database -open -shm -into waves.shm waves -default
database -open -vcd -into verilog.dump _verilog.dump1 -timescale fs
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master.uvc.scl top.i2c_vif_master.uvc.sda top.i2c_vif_master.uvc.uvc_scl top.i2c_vif_master.uvc.uvc_sda top.i2c_vif_slave.uvc.scl top.i2c_vif_slave.uvc.sda top.i2c_vif_slave.uvc.uvc_scl top.i2c_vif_slave.uvc.uvc_sda
probe -create -database waves top.i2c_vif_master_2.uvc.uvc_scl top.i2c_vif_master_2.uvc.uvc_sda
probe -create -database waves top.sda top.scl

simvision -input restore.tcl.svcf
