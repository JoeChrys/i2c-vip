/* 
    Test new code here, leave the poor i2c_random_test alone
*/

class i2c_testing_test extends i2c_base_test;
  `uvm_component_utils(i2c_testing_test)

  i2c_virtual_write_with_stop_no_delays_no_cs v_seq;
      
  extern function new(string name = "i2c_testing_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual function void init_virtual_seq(i2c_virtual_base_sequence virtual_sequence);
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_testing_test:: new(string name = "i2c_testing_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction : new

//-------------------------------------------------------------------------------------------------------------
function void i2c_testing_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  v_seq = i2c_virtual_write_with_stop_no_delays_no_cs :: type_id :: create ("v_seq");
endfunction : build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_testing_test:: start_of_simulation_phase(uvm_phase phase);    
  super.start_of_simulation_phase(phase);   
endfunction

//-------------------------------------------------------------------------------------------------------------
task i2c_testing_test:: run_phase (uvm_phase phase);        
  // super.run_phase(phase);
  phase.raise_objection(this);
  #(cfg.get_delay(FULL)*100);
  
  // init_virtual_seq(v_seq);
  if (!v_seq.randomize() with {
    // start_condition;
    // stop_condition;
  }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
  v_seq.start(null);

  #(cfg.get_delay(FULL)*100);
  phase.drop_objection (this);
endtask
  
//---------------------------------------------------------------------------------------------------------------------
function void i2c_testing_test:: report_phase(uvm_phase phase);
  super.report_phase(phase);
endfunction

function void i2c_testing_test:: init_virtual_seq(i2c_virtual_base_sequence virtual_sequence);
  virtual_sequence.m_seqr = env.master_agent.m_seqr;
  virtual_sequence.s_seqr = env.slave_agent.s_seqr;
  if (virtual_sequence.m_seqr == null) `uvm_fatal("NULPTR", "Master Sequencer has not be set")
  if (virtual_sequence.s_seqr == null) `uvm_fatal("NULPTR", "Slave Sequencer has not be set")
endfunction

