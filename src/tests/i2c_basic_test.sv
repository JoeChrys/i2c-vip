class i2c_basic_test extends i2c_base_test;
  `uvm_component_utils(i2c_basic_test)

  i2c_virtual_base_sequence v_seq0;
  i2c_virtual_write_with_stop_no_delays_no_cs v_seq1;
      
  extern function new(string name = "i2c_basic_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_basic_test:: new(string name = "i2c_basic_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction // new

//-------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  v_seq0 = i2c_virtual_base_sequence::type_id::create ("v_seq0");
  v_seq1 = i2c_virtual_write_with_stop_no_delays_no_cs::type_id::create ("v_seq1");
endfunction // build_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_basic_test:: run_phase (uvm_phase phase);
  unsigned int N = 100;   

  super.run_phase(phase);
  phase.raise_objection(this);
  #(cfg.get_delay(FULL)*100);
  
  // *** Basic test ***

  // * Test basic Addressing *
  // Start - Address (Write) - Reg/Data - Stop
  for (int i=0; i<N; i++) begin
  
    if (!v_seq0.randomize() with {
      !data[7:1] inside {RESERVED_ADDRESSES}; //!
      data[0] == `W; //!
      transaction_type == WRITE;
      start_condition;
      ack_nack == `ACK; //!
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq.start(env.v_seqr);
    if (!v_seq0.randomize() with {
      transaction_type == WRITE; //!
      stop_condition; //!
      ack_nack == `ACK; //!
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq.start(env.v_seqr);

  end

  // Repeat above without stop condition (should yield similar results)
  for (int i=0; i<N; i++) begin
  
    if (!v_seq0.randomize() with {
      !data[7:1] inside {RESERVED_ADDRESSES}; //!
      data[0] == `W; //!
      transaction_type == WRITE;
      start_condition;
      ack_nack == `ACK; //!
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq.start(env.v_seqr);
    if (!v_seq0.randomize() with {
      transaction_type == WRITE; //!
      ack_nack == `ACK; //!
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq.start(env.v_seqr);

  end

  // * Test basic Write *
  for (int i=0; i<N; i++) begin
  
    if (!v_seq1.randomize() with {
      // num_of_bytes
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq.start(env.v_seqr);

  end

  #(cfg.get_delay(FULL)*100);
  phase.drop_objection (this);
endtask // run_phase
  
//---------------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: report_phase(uvm_phase phase);
  super.report_phase(phase);
endfunction // report_phase

