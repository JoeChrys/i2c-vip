/*
      * * * Environment class, by default creates two agents and scoreboard.
            One agent is configured as Master, other as Slave.
            Both agent's monitors are connected to Scoreboards through Analysis ports.
            Feel free to adapt ENV to meet your specific needs.
*/


class i2c_env extends uvm_env;

    `uvm_component_param_utils(i2c_env)

    i2c_env_cfg     cfg_env;
    i2c_agent       master_agent;
    i2c_agent       slave_agent;
    i2c_sb          sb; 

    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual function void connect_phase (uvm_phase phase);
    extern virtual function void start_of_simulation_phase (uvm_phase phase);
    extern virtual function void print_cfg();
endclass : i2c_env

function i2c_env:: new (string name, uvm_component parent);
    super.new(name, parent);
endfunction : new

function void i2c_env:: build_phase (uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db # (i2c_env_cfg) :: get (this, "", "cfg_env", cfg_env)) begin
        `uvm_fatal (get_type_name(), "Failed to get the configuration file from the config DB!")
    end 
    
    master_agent = i2c_agent :: type_id :: create ("master_agent", this);
    slave_agent = i2c_agent :: type_id :: create ("slave_agent", this);

    master_agent.cfg = cfg_env.master_config;
    slave_agent.cfg = cfg_env.slave_config;

        

    sb = i2c_sb::type_id::create("sb",this);
    
endfunction : build_phase 
 
function void i2c_env:: connect_phase (uvm_phase phase);
    super.connect_phase(phase);

    // Connect monitors to scoreboard
    if (cfg_env.connect_master_to_sb) begin
    master_agent.m_mon.i2c_mon_analysis_port.connect(sb.m_mon_imp);
    end
    if (cfg_env.connect_slave_to_sb) begin    
    slave_agent.m_mon.i2c_mon_analysis_port.connect(sb.s_mon_imp); 
    end

endfunction : connect_phase

function void i2c_env:: start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);

    // Disable verbosity of unconnected monitors
    if (!cfg_env.connect_master_to_sb) begin
        master_agent.m_mon.set_report_verbosity_level_hier(UVM_NONE);
    end
    if (!cfg_env.connect_slave_to_sb) begin
        slave_agent.m_mon.set_report_verbosity_level_hier(UVM_NONE);
    end
endfunction : start_of_simulation_phase

function void i2c_env:: print_cfg();
   `uvm_info(get_type_name(), $sformatf ("The configuration that was set : \n%s", cfg_env.sprint()), UVM_MEDIUM)
endfunction : print_cfg


