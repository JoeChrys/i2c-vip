`ifndef I2C_ENV_PKG_SV
`define I2C_ENV_PKG_SV

`timescale 1ns/1ns
`include "uvm_macros.svh" 
`include "i2c_pkg.sv"

package i2c_env_pkg;
  import uvm_pkg::*;
  import i2c_pkg::*;

  `include "i2c_env_cfg.sv"
  `include "i2c_coverage.sv"
  `include "i2c_scoreboard.sv"
  `include "i2c_virtual_sequencer.sv"
  `include "i2c_env.sv"
  
  `include "i2c_virtual_base_sequence.sv"
  `include "i2c_virtual_sequence.sv"
  `include "i2c_test_list.sv"
endpackage 

`endif //I2C_ENV_PKG_SV