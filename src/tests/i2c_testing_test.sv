/* 
    Test new code here, leave the poor i2c_random_test alone
*/

class i2c_testing_test extends i2c_base_test;
  `uvm_component_utils(i2c_testing_test)

  i2c_virtual_sequence#(i2c_master_read_with_stop_with_delays, i2c_slave_write_with_clock_stretch_all) v_seq;
  i2c_virtual_write_with_stop_with_delays_with_cs_all v_seq1;
  i2c_master_write_with_stop_with_delays m_seq;
  i2c_slave_read_with_clock_stretch_all s_seq;

  i2c_virtual_cbus v_seq2;
  i2c_virtual_other_bus v_seq3;
      
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
  
  v_seq = i2c_virtual_sequence#(i2c_master_read_with_stop_with_delays, i2c_slave_write_with_clock_stretch_all) :: type_id :: create ("v_seq");
  v_seq1 = i2c_virtual_write_with_stop_with_delays_with_cs_all::type_id::create("v_seq1");
  m_seq = i2c_master_write_with_stop_with_delays :: type_id :: create ("m_seq");
  s_seq = i2c_slave_read_with_clock_stretch_all :: type_id :: create ("s_seq");
  v_seq2 = i2c_virtual_cbus::type_id::create("v_seq2");
  v_seq3 = i2c_virtual_other_bus::type_id::create("v_seq3");
endfunction

//-------------------------------------------------------------------------------------------------------------
task i2c_testing_test:: run_phase (uvm_phase phase);
  super.run_phase(phase);
  
  phase.raise_objection(this);
  #(cfg.get_delay(FULL)*10);
  
  for (int i=0; i<20; i++) begin
    if (!v_seq3.randomize() with {
      number_of_bytes == 5;
      stop_condition dist {0:=1, 1:=1};
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq3.start(env.v_seqr);
  end

  #(cfg.get_delay(FULL)*10);
  
  // if (!v_seq.randomize() with {
  //   //constraints
  // }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
  // v_seq.start(env.v_seqr);

  // #(cfg.get_delay(FULL)*10);

  // fork
  //   begin
  //     m_seq.randomize() with {number_of_bytes == 5;};
  //     m_seq.start(env.v_seqr.m_seqr);
  //   end
  //   begin
  //     s_seq.randomize() with {number_of_bytes == 5;};
  //     s_seq.start(env.v_seqr.s_seqr);
  //   end
  // join

  #(cfg.get_delay(FULL)*10);
  phase.drop_objection (this);
endtask
