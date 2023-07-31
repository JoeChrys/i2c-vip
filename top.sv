
`include "uvm_macros.svh"
`include "i2c_env_pkg.sv"

module top;
    
    import uvm_pkg::*;
    import i2c_pkg::*;
    import i2c_env_pkg::*;

      
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
    
    i2c_if#(32,32)i2c_vif (system_clock,reset_n);

    //interface
    initial begin
        uvm_config_db#(virtual i2c_if#(32,32))::set(null,"*", "i2c_vif", i2c_vif);
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

