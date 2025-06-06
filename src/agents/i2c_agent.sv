class i2c_agent extends uvm_agent;
  `uvm_component_utils(i2c_agent)

  virtual i2c_if i2c_vif;
    
  i2c_cfg                 cfg;
  i2c_monitor             m_mon;
  i2c_master_driver       m_drv;
  i2c_master_sequencer    m_seqr;
  i2c_slave_driver        s_drv;
  i2c_slave_sequencer     s_seqr;
  
  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase (uvm_phase phase);
  extern virtual function void connect_phase (uvm_phase phase);
endclass // i2c_agent

//-------------------------------------------------------------------------------------------------------------
function i2c_agent:: new(string name, uvm_component parent);
  super.new(name, parent);
endfunction // i2c_agent::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_agent:: build_phase(uvm_phase phase);
  super.build_phase(phase);

  // Get the configuration from the configuration database
  if (!uvm_config_db#(virtual i2c_if)::get(this, "*", "i2c_vif", i2c_vif)) begin
    `uvm_fatal("build_phase_i2c_agent", "interface was not set");
  end else 
    `uvm_info("build_phase_i2c_agent", "i2c_if was set through config db", UVM_LOW); 

  // If agent is active create the driver and sequencer
  if (get_is_active() == UVM_ACTIVE && cfg.agent_type == MASTER) begin // Agent is configured as Master
    this.m_drv = i2c_master_driver::type_id::create("m_drv",this);
    this.m_seqr = i2c_master_sequencer::type_id::create("m_seqr",this);
    `uvm_info("build_phase_master_agent", "Master driver and sequencer created.", UVM_LOW);
  end 
  if (get_is_active() == UVM_ACTIVE && cfg.agent_type == SLAVE) begin // Agent is configured as Slave
    this.s_drv = i2c_slave_driver::type_id::create("s_drv",this);
    this.s_seqr = i2c_slave_sequencer::type_id::create("s_seqr",this);
    `uvm_info("build_phase_slave_agent", "Slave driver and sequencer created.", UVM_LOW);
  end 
  m_mon = i2c_monitor::type_id::create("m_mon", this);
endfunction // i2c_agent::buid_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_agent:: connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    // If agent is active connect the driver to the sequencer
    if (get_is_active() == UVM_ACTIVE &&  cfg.agent_type == MASTER) begin  //
        m_drv.seq_item_port.connect(m_seqr.seq_item_export);
        `uvm_info("connect_phase_i2c_agent", "master driver connected.", UVM_LOW);
    end
    if (get_is_active() == UVM_ACTIVE &&  cfg.agent_type == SLAVE) begin  //
        s_drv.seq_item_port.connect(s_seqr.seq_item_export);
        `uvm_info("connect_phase_i2c_agent", "slave driver connected.", UVM_LOW);
    end
endfunction // i2c_agent::connect_phase

