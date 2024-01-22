// *** Multimaster Env

class i2c_multimaster_env extends i2c_env;
  `uvm_component_param_utils(i2c_multimaster_env)

  i2c_agent       master_agent_2;

  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase (uvm_phase phase);
  extern virtual function void connect_phase (uvm_phase phase);
  extern virtual function void start_of_simulation_phase (uvm_phase phase);
endclass // i2c_multimaster_env

function i2c_multimaster_env:: new (string name, uvm_component parent);
  super.new(name, parent);
endfunction // i2c_multimaster_env::new

function void i2c_multimaster_env:: build_phase (uvm_phase phase);
  super.build_phase(phase);
  
  master_agent_2 = i2c_agent :: type_id :: create ("master_agent", this);
  master_agent_2.cfg = cfg_env.master_config;
endfunction // i2c_multimaster_env::build_phase 
 
function void i2c_multimaster_env:: connect_phase (uvm_phase phase);
  super.connect_phase(phase);
endfunction // i2c_multimaster_env::connect_phase

function void i2c_multimaster_env:: start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);

  // Disable verbosity of unconnected monitors
  if (!cfg_env.connect_master_to_sb) begin
    master_agent_2.m_mon.set_report_verbosity_level_hier(UVM_NONE);
  end
endfunction // i2c_multimaster_env::start_of_simulation_phase