/* 
    Test new code here, leave the poor i2c_random_test alone
*/

class i2c_testing_test extends i2c_base_test;
  `uvm_component_utils(i2c_testing_test)

  // i2c_virtual_write_with_stop_no_delays_no_cs v_seq;
  i2c_virtual_sequence#(i2c_master_read_with_stop_with_delays, i2c_slave_write_with_clock_stretch_ack) v_seq;
      
  extern function new(string name = "i2c_testing_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_testing_test:: new(string name = "i2c_testing_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction

//-------------------------------------------------------------------------------------------------------------
function void i2c_testing_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  v_seq = i2c_virtual_sequence#(i2c_master_read_with_stop_with_delays, i2c_slave_write_with_clock_stretch_ack) :: type_id :: create ("v_seq");
endfunction

//-------------------------------------------------------------------------------------------------------------
task i2c_testing_test:: run_phase (uvm_phase phase);
  super.run_phase(phase);
  
  phase.raise_objection(this);
  #(cfg.get_delay(FULL)*10);
  
  init_virtual_seq(v_seq);
  if (!v_seq.randomize() with {
    //constraints
  }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
  v_seq.start(null);

  #(cfg.get_delay(FULL)*10);
  phase.drop_objection (this);
endtask
