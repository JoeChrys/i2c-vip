/*
  Default configuration is one master and one slave agent for the test. You can set up environment cfg here.
*/
class i2c_base_test extends uvm_test;
  
  int iterations = 10;
  int number_of_bytes = 3;

  `uvm_component_utils(i2c_base_test)

  i2c_cfg cfg;

  i2c_env_cfg cfg_env;
  i2c_env env;

  virtual i2c_if i2c_vif_master;
  virtual i2c_if i2c_vif_slave;
  
  i2c_master_start_byte m_start_byte;
  i2c_master_high_speed_mode m_high_speed_mode;

  extern function new(string name = "i2c_base_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);

  extern virtual function void cfg_randomize(); 
  extern virtual function void set_default_configuration ();
  extern virtual task bus_setup();
endclass // i2c_base_test

//-------------------------------------------------------------------------------------------------------------
function  i2c_base_test:: new(string name = "i2c_base_test", uvm_component parent=null);
	super.new(name,parent);
endfunction // i2c_base_test::new

//-------------------------------------------------------------------------------------------------------------
function void  i2c_base_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);

  if(!uvm_config_db#(virtual i2c_if)::get(this, "", "i2c_vif_master", i2c_vif_master)) 
    `uvm_fatal("build_phase",{"virtual interface must be set for: ", get_full_name(),".i2c_vif_master"});
  if(!uvm_config_db#(virtual i2c_if)::get(this, "", "i2c_vif_slave", i2c_vif_slave)) 
    `uvm_fatal("build_phase",{"virtual interface must be set for: ", get_full_name(),".i2c_vif_slave"});

  cfg_env = i2c_env_cfg::type_id::create("cfg_env", this);
  env = i2c_env::type_id::create("env", this);
  `uvm_info("build_phase", "Enviroment created.", UVM_HIGH)

  cfg = i2c_cfg::type_id::create("cfg", this);
  cfg_randomize();

  set_default_configuration();
  cfg_env.master_config.agent_type = MASTER;
  cfg_env.slave_config.agent_type = SLAVE;

  uvm_config_db#(virtual i2c_if)::set(this,"env.master_agent.*","i2c_vif", i2c_vif_master);
  uvm_config_db#(virtual i2c_if)::set(this,"env.slave_agent.*","i2c_vif", i2c_vif_slave);

  uvm_config_db#(i2c_env_cfg)::set(this,"env","cfg_env", cfg_env);
  uvm_config_db#(i2c_cfg)::set(this, "*", "cfg", cfg);

  m_start_byte = i2c_master_start_byte::type_id::create("m_start_byte");
  m_high_speed_mode = i2c_master_high_speed_mode::type_id::create("m_high_speed_mode");
endfunction // i2c_base_test::build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_base_test:: end_of_elaboration_phase(uvm_phase phase);
  uvm_verbosity verbosity = UVM_LOW;
  super.end_of_elaboration_phase(phase);

  //set verbosity level for env
  void'( $value$plusargs("VERBOSITY=%s", verbosity) );
  `uvm_info("end_of_elaboration_phase", $sformatf("Verbosity is set to %s.", verbosity.name()), UVM_LOW)
	env.set_report_verbosity_level_hier(verbosity);
endfunction // i2c_base_test::end_of_elaboration_phase

//-------------------------------------------------------------------------------------------------------------
function void  i2c_base_test:: start_of_simulation_phase(uvm_phase phase);
	uvm_report_server svr;
	super.start_of_simulation_phase(phase);

	uvm_top.set_timeout(.timeout(this.cfg.test_time_out), .overridable(1));
	`uvm_info("start_of_simulation_phase", $sformatf("Printing topology"), UVM_LOW)
	uvm_top.print_topology();
	svr = uvm_report_server::get_server();
	svr.set_max_quit_count(20); //maximum number of errors

  // [optional] use ::get(null, "uvm_test_top", "m_seqr", m_seqr) to get sequencer from test
  uvm_config_db#(i2c_master_sequencer)::set(this,"","m_seqr", env.master_agent.m_seqr);
  uvm_config_db#(i2c_slave_sequencer)::set(this,"","s_seqr", env.slave_agent.s_seqr); 
endfunction // i2c_base_test::start_of_simulation_phase

//-------------------------------------------------------------------------------------------------------------
function void  i2c_base_test:: report_phase(uvm_phase phase);
  uvm_report_server svr;
  super.report_phase(phase);

  svr = uvm_report_server::get_server();
  if (svr.get_severity_count(UVM_ERROR) != 0) begin
    `uvm_fatal("report_phase", "Test failed!")
  end
endfunction // i2c_base_test::report_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_base_test:: cfg_randomize(); 
 	if (!cfg.randomize() with {
    //add constraints

    })
  `uvm_fatal("build_phase","Configuration randomization failed");
endfunction // i2c_base_test::cfg_randomize

//-------------------------------------------------------------------------------------------------------------
function void i2c_base_test:: set_default_configuration ();
  `uvm_info("config", "Default configuration set.", UVM_HIGH)
endfunction // i2c_base_test::set_default_configuration

//-------------------------------------------------------------------------------------------------------------
task i2c_base_test:: bus_setup();
  if (cfg.slave_driver_type == POLLING_CPU && !env.slave_agent.m_mon.bus_active) begin
    if (!m_start_byte.randomize()) `uvm_error("RNDERR", "Start Byte Sequence Randomization failed")
    m_start_byte.start(env.master_agent.m_seqr);
  end
  if (cfg.high_speed_only && cfg.current_speed_mode == cfg.default_speed_mode) begin
    if (!m_high_speed_mode.randomize()) `uvm_error("RNDERR", "High Speed Mode Sequence Randomization failed")
    m_high_speed_mode.start(env.master_agent.m_seqr);
  end
endtask // bus_setup