`ifndef I2C_PKG_SV
`define I2C_PKG_SV

`include "uvm_macros.svh"
`include "i2c_if.sv"

package i2c_pkg;
  import uvm_pkg::*;
  
  `include "i2c_defines.sv"
  `include "i2c_cfg.sv"
  `include "i2c_item.sv"
  `include "i2c_monitor.sv" 
  `include "i2c_master_sequencer.sv"
  `include "i2c_slave_sequencer.sv"
  `include "i2c_master_base_sequence.sv"
  `include "i2c_master_sequence.sv"
  `include "i2c_slave_base_sequence.sv"
  `include "i2c_slave_sequence.sv"
  `include "i2c_master_driver.sv"
  `include "i2c_slave_driver.sv"
  `include "i2c_agent.sv"
endpackage 

`endif //I2C_PKG_SV

