class i2c_basic_test extends i2c_base_test;
  `uvm_component_utils(i2c_basic_test)

  i2c_virtual_write_with_stop_no_delays_no_cs v_seq10;
  i2c_virtual_read_with_stop_no_delays_no_cs v_seq11;
  i2c_virtual_write_no_stop_no_delays_no_cs v_seq20;
  i2c_virtual_read_no_stop_no_delays_no_cs v_seq21;
      
  extern function new(string name = "i2c_basic_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_basic_test:: new(string name = "i2c_basic_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction // new

//-------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  v_seq10 = i2c_virtual_write_with_stop_no_delays_no_cs::type_id::create("v_seq10");
  v_seq11 = i2c_virtual_read_with_stop_no_delays_no_cs::type_id::create("v_seq11");
  v_seq20 = i2c_virtual_write_no_stop_no_delays_no_cs::type_id::create("v_seq20");
  v_seq21 = i2c_virtual_read_no_stop_no_delays_no_cs::type_id::create("v_seq21");
endfunction // build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
  // already defaults
  //cfg.has_coverage = 1;
  //cfg.high_speed_only = 0;
  //cfg.slave_driver_type = PERIPHERAL_DEVICE;
endfunction // start_of_simulation_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_basic_test:: run_phase (uvm_phase phase);
  super.run_phase(phase);
  phase.raise_objection(this);

  #(cfg.get_delay(FULL)*100);

  for (int i=0; i<iterations; i++) begin
    bus_setup();

    randcase
      1:  begin
            if (!v_seq10.randomize() with {
              number_of_bytes == local::number_of_bytes;
            }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
            v_seq10.start(env.v_seqr);
          end
      1:  begin
            if (!v_seq11.randomize() with {
              number_of_bytes == local::number_of_bytes;
            }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
            v_seq11.start(env.v_seqr);
          end
      1:  begin
            if (!v_seq20.randomize() with {
              number_of_bytes == local::number_of_bytes;
            }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
            v_seq20.start(env.v_seqr);
          end
      1:  begin
            if (!v_seq21.randomize() with {
              number_of_bytes == local::number_of_bytes;
            }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
            v_seq21.start(env.v_seqr);
          end
    endcase

    cfg.master_finish.wait_trigger();
  end

  #(cfg.get_delay(FULL)*100);

  phase.drop_objection (this);
endtask // run_phase

