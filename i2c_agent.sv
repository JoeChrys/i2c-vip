
class i2c_agent#(parameter int ADDR = 32,parameter int DATA = 32) extends uvm_agent;
    
    `uvm_component_utils(i2c_agent#(ADDR,DATA))

    virtual i2c_if#(ADDR, DATA) i2c_vif;
      
    i2c_cfg                 cfg;
    i2c_monitor#(ADDR, DATA)            m_mon;
    i2c_master_driver#(ADDR, DATA)       m_drv;
    i2c_master_sequencer    m_seqr;
    i2c_slave_driver#(ADDR, DATA)        s_drv;
    i2c_slave_sequencer     s_seqr;
   
    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual function void connect_phase (uvm_phase phase);
    
endclass //i2c_agent

//-------------------------------------------------------------------------------------------------------------
function i2c_agent::new(string name, uvm_component parent);
    super.new(name, parent);
    `uvm_info("i2c_agent", "i2c UVC", UVM_LOW);
endfunction

//-------------------------------------------------------------------------------------------------------------
function void i2c_agent::build_phase(uvm_phase phase);
    
    super.build_phase(phase);

    if (!uvm_config_db#(virtual i2c_if#(ADDR, DATA))::get(this, "*", "i2c_vif", i2c_vif)) begin
        `uvm_fatal("build_phase_i2c_agent", "interface was not set");
    end else 
        `uvm_info("build_phase_i2c_agent", "i2c_if was set through config db", UVM_LOW); 

    `uvm_info("AGENT", $sformatf("cfg.agent_type = %0b", cfg.agent_type), UVM_LOW)

     if (get_is_active() == UVM_ACTIVE && cfg.agent_type == MASTER) begin // Agent is configured as Master
        this.m_drv = i2c_master_driver#(ADDR, DATA)::type_id::create("m_drv",this);
        this.m_seqr = i2c_master_sequencer::type_id::create("m_seqr",this);
        `uvm_info("build_phase_master_agent", "Master driver and sequencer created.", UVM_LOW);
    end 
    if (get_is_active() == UVM_ACTIVE && cfg.agent_type == SLAVE) begin // Agent is configured as Slave
        this.s_drv = i2c_slave_driver#(ADDR, DATA)::type_id::create("s_drv",this);
        this.s_seqr = i2c_slave_sequencer::type_id::create("s_seqr",this);
        `uvm_info("build_phase_master_agent", "Slave driver and sequencer created.", UVM_LOW);
    end 
    m_mon = i2c_monitor#(ADDR, DATA)::type_id::create("m_mon", this);
    //print_config();
endfunction // i2c_master_agent::buid_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_agent::connect_phase(uvm_phase phase);
    if (get_is_active() == UVM_ACTIVE &&  cfg.agent_type == 0) begin  //
        m_drv.seq_item_port.connect(m_seqr.seq_item_export);
        `uvm_info("connect_phase_i2c_agent", "master driver connected.", UVM_LOW);
    end
    if (get_is_active() == UVM_ACTIVE &&  cfg.agent_type == 1) begin  //
        s_drv.seq_item_port.connect(s_seqr.seq_item_export);
        `uvm_info("connect_phase_i2c_agent", "slave driver connected.", UVM_LOW);
    end
   //  i2c_vif.i2c_baud_rate_value <= cfg.i2c_baud_rate_divisor;
endfunction // i2c_agent::connect_phase

