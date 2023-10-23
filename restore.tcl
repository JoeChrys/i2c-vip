
# XM-Sim Command File
# TOOL:	xmsim(64)	22.03-s002
#
#
# You can restore this configuration with:
#
#      xrun top.sv -timescale 1ps/1ps -sysv -access +rw -uvm -seed random -uvmhome CDNS-1.2 +UVM_TESTNAME=i2c_random_test -clean -l i2c_random_test.log +DUMPNAME=i2c_random_test.vcd +VERBOSITY=UVM_DEBUG -s -input restore.tcl
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
set svseed -497505354
set assert_reporting_mode 0
set vcd_compact_mode 0
alias . run
alias quit exit
stop -create -name Randomize -randomize
database -open -vcd -into i2c_random_test.vcd _i2c_random_test.vcd1 -timescale fs
database -open -shm -into xcelium.shm xcelium.shm -default
database -open -shm -into waves.shm _waves.shm
database -open -vcd -into verilog.dump _verilog.dump1 -timescale fs
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.super i2c_pkg::i2c_item::type_name
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.req \$uvm:{uvm_test_top.env.master_agent.m_drv}.rsp -all -depth  2
probe -create -database xcelium.shm i2c_pkg::i2c_master_driver::type_name \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top}.m_seq \$uvm:{uvm_test_top}.s_seq \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv}.rsp_port \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_port \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.super i2c_pkg::i2c_item::type_name
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.req \$uvm:{uvm_test_top.env.master_agent.m_drv}.rsp -all -depth  2
probe -create -database xcelium.shm i2c_pkg::i2c_master_driver::type_name \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top}.m_seq \$uvm:{uvm_test_top}.s_seq \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv}.rsp_port \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_port \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.super i2c_pkg::i2c_item::type_name
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.req \$uvm:{uvm_test_top.env.master_agent.m_drv}.rsp -all -depth  2
probe -create -database xcelium.shm i2c_pkg::i2c_master_driver::type_name \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top}.m_seq \$uvm:{uvm_test_top}.s_seq \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv}.rsp_port \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_port \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.super i2c_pkg::i2c_item::type_name
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.req \$uvm:{uvm_test_top.env.master_agent.m_drv}.rsp -all -depth  2
probe -create -database xcelium.shm i2c_pkg::i2c_master_driver::type_name \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top}.m_seq \$uvm:{uvm_test_top}.s_seq \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv}.rsp_port \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_port \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.super i2c_pkg::i2c_item::type_name
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv}.req \$uvm:{uvm_test_top.env.master_agent.m_drv}.rsp -all -depth  2
probe -create -database xcelium.shm i2c_pkg::i2c_master_driver::type_name \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top}.m_seq \$uvm:{uvm_test_top}.s_seq \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.slave_agent.s_drv}.rsp_port \$uvm:{uvm_test_top.env.slave_agent.s_drv}.seq_item_port \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv}.seq_item_prod_if \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv.rsp_port} \$uvm:{uvm_test_top.env.master_agent.m_drv.seq_item_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.rsp_port} \$uvm:{uvm_test_top.env.slave_agent.s_drv.seq_item_port} \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm \$uvm:{uvm_test_top.env.master_agent.m_drv} \$uvm:{uvm_test_top.env.slave_agent.s_drv} -all -depth all
probe -create -database xcelium.shm top.i2c_vif_master.__assert_1 top.i2c_vif_master.__assert_2 top.i2c_vif_master.__assert_3 top.i2c_vif_master.__assert_4 top.i2c_vif_master.__assert_5 top.i2c_vif_master.__assert_6
probe -create -database xcelium.shm top.i2c_vif_master.sda top.i2c_vif_master.scl top.i2c_vif_master.uvc_sda top.i2c_vif_master.uvc_scl top.i2c_vif_master.reset_n top.i2c_vif_master.system_clock
probe -create -database xcelium.shm top.i2c_vif_slave.__assert_1 top.i2c_vif_slave.__assert_2 top.i2c_vif_slave.__assert_3 top.i2c_vif_slave.__assert_4 top.i2c_vif_slave.__assert_5 top.i2c_vif_slave.__assert_6
probe -create -database xcelium.shm top.i2c_vif_slave.uvc_sda top.i2c_vif_slave.uvc_scl top.i2c_vif_slave.sda top.i2c_vif_slave.scl top.i2c_vif_slave.reset_n top.i2c_vif_slave.system_clock
probe -create -database xcelium.shm

simvision -input restore.tcl.svcf
