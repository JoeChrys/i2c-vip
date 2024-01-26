class i2c_virtual_sequencer extends uvm_sequencer;
  `uvm_component_utils(i2c_virtual_sequencer)

  i2c_cfg cfg;

  i2c_master_sequencer m_seqr;
  i2c_master_sequencer m_seqr_2;
  i2c_slave_sequencer s_seqr;

  extern function new (string name, uvm_component parent);
  extern function void build_phase (uvm_phase phase);
endclass // i2c_virtual_sequencer

//-------------------------------------------------------------------------------------------------------------
function i2c_virtual_sequencer:: new (string name, uvm_component parent);
  super.new(name, parent);
endfunction // i2c_virtual_sequencer::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_virtual_sequencer:: build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if (!uvm_config_db#(i2c_cfg )::get(this, "", "cfg", cfg)) begin
    `uvm_info("build_phase", "CFG is not set through config db", UVM_LOW);    
  end 
  else begin
    `uvm_info("build_phase", "CFG is set through config db", UVM_LOW);
  end
endfunction // i2c_virtual_sequencer::build_phase