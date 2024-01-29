class i2c_basic_test extends i2c_base_test;
  N = 100;
  number_of_bytes = 3;

  `uvm_component_utils(i2c_basic_test)

  i2c_virtual_base_sequence v_seq00;
  i2c_virtual_multibyte_sequence v_seq01;
  i2c_virtual_write_with_stop_no_delays_no_cs v_seq10;

  param_struct param_q[$];
  param_struct rand_with;
      
  extern function new(string name = "i2c_basic_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual fucntion void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
  extern virtual function void reset_params(ref param_struct ps);
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_basic_test:: new(string name = "i2c_basic_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction // new

//-------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  v_seq00 = i2c_virtual_base_sequence::type_id::create ("v_seq00");
  v_seq01 = i2c_virtual_multibyte_sequence::type_id::create ("v_seq01");
  v_seq10 = i2c_virtual_write_with_stop_no_delays_no_cs::type_id::create ("v_seq10");
endfunction // build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);

  cfg.has_coverage = 0;

  // *** Write with stop ***
  reset_params();
  param_q.push_back(rand_with);

  // *** Write without stop ***
  rand_with.stop_condition = 0;
  param_q.push_back(rand_with);

  // *** Read with stop ***
  reset_params();
  rand_with.transaction_type = READ;
  rand_with.data0 = `R;
  param_q.push_back(rand_with);

  // *** Read without stop ***
  rand_with.stop_condition = 0;
  param_q.push_back(rand_with);


endfunction // start_of_simulation_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_basic_test:: run_phase (uvm_phase phase);
  super.run_phase(phase);
  phase.raise_objection(this);
  #(cfg.get_delay(FULL)*100);
  
  // *** Basic test ***

  // * Test basic Addressing *
  for (int i = 0; i < param_q.size(); i++) begin
    rand_with = param_q[i];
    repeat(N) begin
    
      if (!v_seq00.randomize() with {
        !(data[7:1] inside {RESERVED_ADDRESSES}); //!
        data[0] == rand_with.data0; //!
        transaction_type == rand_with.transaction_type;
        start_condition = rand_with.start_condition;
        ack_nack == `ACK; //!
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);
      if (!v_seq00.randomize() with {
        transaction_type == rand_with.transaction_type; //!
        stop_condition == rand_with.stop_condition; //!
        ack_nack == rand_with.ack_nack; //!
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);

    end
  end

  // * Repeat test with master delay
  for (int i = 0; i < param_q.size(); i++) begin
    rand_with = param_q[i];
    repeat(N) begin
    
      if (!v_seq00.randomize() with {
        !(data[7:1] inside {RESERVED_ADDRESSES}); //!
        data[0] == rand_with.data0; //!
        transaction_type == rand_with.transaction_type;
        start_condition = rand_with.start_condition;
        ack_nack == `ACK; //!
        delay inside {[10:100]};
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);
      if (!v_seq00.randomize() with {
        transaction_type == rand_with.transaction_type; //!
        stop_condition == rand_with.stop_condition; //!
        ack_nack == rand_with.ack_nack; //!
        delay inside {[10:100]};
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);

    end
  end

  // Repeat with full clock stretch
  for (int i = 0; i < param_q.size(); i++) begin
    rand_with = param_q[i];
    repeat(N) begin
    
      if (!v_seq00.randomize() with {
        !(data[7:1] inside {RESERVED_ADDRESSES}); //!
        data[0] == rand_with.data0; //!
        transaction_type == rand_with.transaction_type;
        start_condition = rand_with.start_condition;
        ack_nack == `ACK; //!
        clock_stretch_ack inside {[5:20]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[1:10]};}
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);
      if (!v_seq00.randomize() with {
        transaction_type == rand_with.transaction_type; //!
        stop_condition == rand_with.stop_condition; //!
        ack_nack == rand_with.ack_nack; //!
        clock_stretch_ack inside {[5:20]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[1:10]};}
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);

    end
  end

  // * Repeat test with both master delay and full clock stretch
  for (int i = 0; i < param_q.size(); i++) begin
    rand_with = param_q[i];
    repeat(N) begin
    
      if (!v_seq00.randomize() with {
        !(data[7:1] inside {RESERVED_ADDRESSES}); //!
        data[0] == rand_with.data0; //!
        transaction_type == rand_with.transaction_type;
        start_condition = rand_with.start_condition;
        ack_nack == `ACK; //!
        delay inside {[10:100]};
        clock_stretch_ack inside {[5:20]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[1:10]};}
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);
      if (!v_seq00.randomize() with {
        transaction_type == rand_with.transaction_type; //!
        stop_condition == rand_with.stop_condition; //!
        ack_nack == rand_with.ack_nack; //!
        delay inside {[10:100]};
        clock_stretch_ack inside {[5:20]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[1:10]};}
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);

    end
  end

  // * Test Write *
  for (int i=0; i<N; i++) begin
  
    if (!v_seq10.randomize() with {
      // num_of_bytes
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq10.start(env.v_seqr);

  end

  #(cfg.get_delay(FULL)*100);
  phase.drop_objection (this);
endtask // run_phase
  
//---------------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: reset_params(param_struct ps);
  ps.start_condition = 1;
  ps.stop_condition = 1;
  ps.data0 = `W;
  ps.ack_nack = `ACK;
  ps.transaction_type = WRITE;
endfunction // reset_params

