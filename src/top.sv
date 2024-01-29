
`include "uvm_macros.svh"
`include "i2c_env_pkg.sv"

module top;
  
  import uvm_pkg::*;
  import i2c_pkg::*;
  import i2c_env_pkg::*;

  tri1 sda;
  tri1 scl;
    
  bit system_clock, reset_n;
  
  // 25MHz clock freq for timescale 1ns
  parameter CLK_CYCLE = 20; 
  localparam delay_reset = 105;
  string logfile = "dump.vcd";
    
  // Clock Generation
  initial begin
    system_clock =0;
    forever #(CLK_CYCLE) system_clock = ~system_clock;
  end 

  // Reset Initialization
  initial begin
    reset_n = 0;
    #delay_reset; //async reset
    reset_n = 1;
  end
  
  i2c_if i2c_vif_master (system_clock,reset_n);
  i2c_if i2c_vif_slave  (system_clock,reset_n);
  i2c_if i2c_vif_master_2 (system_clock,reset_n);

  // Connect UVC logic to Top Pull-Up wire (tri1)
  assign sda = i2c_vif_master.uvc_sda;
  assign scl = i2c_vif_master.uvc_scl;
  assign sda = i2c_vif_slave.uvc_sda;
  assign scl = i2c_vif_slave.uvc_scl;
  assign sda = i2c_vif_master_2.uvc_sda;
  assign scl = i2c_vif_master_2.uvc_scl;

  // Connect Top Pull-Up to internal IF wires
  assign i2c_vif_master.sda = sda;
  assign i2c_vif_master.scl = scl;
  assign i2c_vif_slave.sda = sda;
  assign i2c_vif_slave.scl = scl;
  assign i2c_vif_master_2.sda = sda;
  assign i2c_vif_master_2.scl = scl;

  // Set Interface
  initial begin
    uvm_config_db#(virtual i2c_if)::set(null,"uvm_test_top", "i2c_vif_master", i2c_vif_master);
    uvm_config_db#(virtual i2c_if)::set(null,"uvm_test_top", "i2c_vif_slave", i2c_vif_slave);
    uvm_config_db#(virtual i2c_if)::set(null,"uvm_test_top", "i2c_vif_master_2", i2c_vif_master_2);
  end
  
  // invoking simulation phases of all components
  initial begin
    run_test(""); 
  end
  // Waves
  initial begin
    if (!$value$plusargs("DUMPNAME=%s", logfile))
      $warning("DUMPNAME not specified");
    $dumpfile(logfile); 
    $dumpvars;
  end

  // assert that slave will not overlap with masters
  always @(negedge i2c_vif_master.uvc_scl) assert (i2c_vif_slave.uvc_scl !== 0);
  always @(negedge i2c_vif_master_2.uvc_scl) assert (i2c_vif_slave.uvc_scl !== 0);
endmodule 

