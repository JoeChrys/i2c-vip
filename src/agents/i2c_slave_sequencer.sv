class i2c_slave_sequencer extends uvm_sequencer #(i2c_item);
  `uvm_component_utils(i2c_slave_sequencer)

  i2c_cfg cfg;

  extern function new (string name, uvm_component parent);
  extern function void build_phase (uvm_phase phase);
endclass // i2c_slave_sequencer
 
//-------------------------------------------------------------------------------------------------------------
function i2c_slave_sequencer::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction 

//-------------------------------------------------------------------------------------------------------------
function void i2c_slave_sequencer::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg)) begin
    `uvm_info("build_phase", "CFG is not set through config db", UVM_LOW);    
  end  
endfunction


