class i2c_functionality_test extends i2c_base_test;
  int N = 100;
  int number_of_bytes = 3;

  `uvm_component_utils(i2c_functionality_test)

  i2c_virtual_base_sequence v_seq00;
  i2c_virtual_multibyte_sequence v_seq01;

  param_struct param_q[$];
  param_struct rand_with;
      
  extern function new(string name = "i2c_functionality_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
  extern virtual function void reset_params();
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_functionality_test:: new(string name = "i2c_functionality_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction // new

//-------------------------------------------------------------------------------------------------------------
function void i2c_functionality_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  v_seq00 = i2c_virtual_base_sequence::type_id::create ("v_seq00");
  v_seq01 = i2c_virtual_multibyte_sequence::type_id::create ("v_seq01");
endfunction // build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_functionality_test:: start_of_simulation_phase(uvm_phase phase);
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
task i2c_functionality_test:: run_phase (uvm_phase phase);
  super.run_phase(phase);
  phase.raise_objection(this);
  #(cfg.get_delay(FULL)*100);
  
  // *** functionality test ***

  // * Test Addressing *
  for (int i = 0; i < param_q.size(); i++) begin
    rand_with = param_q[i];
    repeat(N) begin
    
      if (!v_seq00.randomize() with {
        !(data[7:1] inside {RESERVED_ADDRESSES}); //!
        data[0] == rand_with.data0; //!
        transaction_type == WRITE;
        start_condition == 1;
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
        transaction_type == WRITE;
        start_condition == 1;
        ack_nack == `ACK; //!
        delay inside {[20:100]};
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);
      if (!v_seq00.randomize() with {
        transaction_type == rand_with.transaction_type; //!
        stop_condition == rand_with.stop_condition; //!
        ack_nack == rand_with.ack_nack; //!
        delay inside {[20:100]};
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
        transaction_type == WRITE;
        start_condition == 1;
        ack_nack == `ACK; //!
        clock_stretch_ack inside {[10:30]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[1:20]};}
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);
      if (!v_seq00.randomize() with {
        transaction_type == rand_with.transaction_type; //!
        stop_condition == rand_with.stop_condition; //!
        ack_nack == rand_with.ack_nack; //!
        clock_stretch_ack inside {[10:30]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[1:20]};}
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
        transaction_type == WRITE;
        start_condition == 1;
        ack_nack == `ACK; //!
        delay inside {[20:100]};
        clock_stretch_ack inside {[5:20]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[10:20]};}
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);
      if (!v_seq00.randomize() with {
        transaction_type == rand_with.transaction_type; //!
        stop_condition == rand_with.stop_condition; //!
        ack_nack == rand_with.ack_nack; //!
        delay inside {[20:100]};
        clock_stretch_ack inside {[5:20]};
        foreach (clock_stretch_data[i]) {clock_stretch_data[i] inside {[10:20]};}
      }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
      v_seq00.start(env.v_seqr);

    end
  end

  #(cfg.get_delay(FULL)*100);
  phase.drop_objection (this);
endtask // run_phase
  
//---------------------------------------------------------------------------------------------------------------------
function void i2c_functionality_test:: reset_params();
  rand_with.stop_condition = 1;
  rand_with.data0 = `W;
  rand_with.ack_nack = `ACK;
  rand_with.transaction_type = WRITE;
endfunction // reset_params

