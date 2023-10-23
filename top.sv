
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
      
    initial begin
        system_clock =0;
        forever #(CLK_CYCLE) system_clock = ~system_clock;
    end 

    //reset initialization
    initial begin
        reset_n = 0;
        #delay_reset; //async reset
        reset_n = 1;
    end
    
    i2c_if i2c_vif_master (system_clock,reset_n);
    i2c_if i2c_vif_slave  (system_clock,reset_n);
    assign sda = i2c_vif_master.uvc_sda;
    assign sda = i2c_vif_slave.uvc_sda;
    assign scl = i2c_vif_master.uvc_scl;
    assign scl = i2c_vif_slave.uvc_scl;

    assign i2c_vif_master.sda = sda;
    assign i2c_vif_master.scl = scl;
    assign i2c_vif_slave.sda = sda;
    assign i2c_vif_slave.scl = scl;

    //interface
    initial begin
        uvm_config_db#(virtual i2c_if)::set(null,"uvm_test_top", "i2c_vif_master", i2c_vif_master);
        uvm_config_db#(virtual i2c_if)::set(null,"uvm_test_top", "i2c_vif_slave", i2c_vif_slave);
    end
    
    // invoking simulation phases of all components
    initial begin
        run_test(""); 
    end
    // Waves
    initial begin
        $value$plusargs("DUMPNAME=%s", logfile);
        $dumpfile(logfile); 
        $dumpvars;
    end
endmodule 

