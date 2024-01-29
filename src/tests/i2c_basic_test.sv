class i2c_basic_test extends i2c_base_test;
  int N = 30;
  int number_of_bytes = 3;

  `uvm_component_utils(i2c_basic_test)

  i2c_master_start_byte m_start_byte;
  i2c_master_high_speed_mode m_high_speed_mode;

  i2c_virtual_write_with_stop_no_delays_no_cs v_seq10;
  i2c_virtual_read_no_stop_no_delays_no_cs v_seq11;
      
  extern function new(string name = "i2c_basic_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase (uvm_phase phase);
  extern virtual task bus_setup();
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_basic_test:: new(string name = "i2c_basic_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction // new

//-------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);

  m_start_byte = i2c_master_start_byte::type_id::create("m_start_byte");
  m_high_speed_mode = i2c_master_high_speed_mode::type_id::create("m_high_speed_mode");
  
  v_seq10 = i2c_virtual_write_with_stop_no_delays_no_cs::type_id::create("v_seq10");
  v_seq11 = i2c_virtual_read_no_stop_no_delays_no_cs::type_id::create("v_seq11");
endfunction // build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_basic_test:: start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
  // already defaults
  //cfg.has_coverage = 1;
  // cfg.high_speed_only = 0;
  //cfg.slave_driver_type = PERIPHERAL_DEVICE;

  cfg.high_speed_only = 1;
  // cfg.slave_driver_type = POLLING_CPU;
endfunction // start_of_simulation_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_basic_test:: run_phase (uvm_phase phase);
  super.run_phase(phase);
  phase.raise_objection(this);
  #(cfg.get_delay(FULL)*100);
  

  // * Test Write *
  for (int i=0; i<N; i++) begin
  
    bus_setup();
    if (!v_seq10.randomize() with {
      number_of_bytes == local::number_of_bytes;
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq10.start(env.v_seqr);
    cfg.master_finish.wait_trigger();

  end

  #(cfg.get_delay(FULL)*100);

  for (int i=0; i<N; i++) begin
  
    bus_setup();
    if (!v_seq11.randomize() with {
      number_of_bytes == local::number_of_bytes;
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq11.start(env.v_seqr);
    cfg.master_finish.wait_trigger();

  end

  #(cfg.get_delay(FULL)*100);
  phase.drop_objection (this);
endtask // run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_basic_test:: bus_setup();
  if (cfg.slave_driver_type == POLLING_CPU && !env.slave_agent.m_mon.bus_active) begin
    if (!m_start_byte.randomize()) `uvm_error("RNDERR", "Start Byte Sequence Randomization failed")
    m_start_byte.start(env.master_agent.m_seqr);
  end
  if (cfg.high_speed_only && cfg.current_speed_mode == cfg.default_speed_mode) begin
    if (!m_high_speed_mode.randomize()) `uvm_error("RNDERR", "High Speed Mode Sequence Randomization failed")
    m_high_speed_mode.start(env.master_agent.m_seqr);
  end
endtask // bus_setup

