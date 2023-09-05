/*
* * * * *   AGENT TIMINGS     * * * * * 
*/

class i2c_timings extends uvm_object;  

//  Timing variables
    speed_mode_enum default_speed_mode;

    int period_SM = 10000; //ns
    int period_FM = 2500;
    int period_FMP = 1000;
    int period_HSM = 300;

//  Default constraints 
    constraint c_default_speed_mode {        
        soft default_speed_mode == SM;
    }
//------------------------------------------------------------------------------------------------------------
// Shorthand macros
//------------------------------------------------------------------------------------------------------------
    // `uvm_object_utils_begin(i2c_timings)
    //     `uvm_field_int (has_coverage, UVM_ALL_ON)
    //     `uvm_field_int (has_checks, UVM_ALL_ON)
    // `uvm_object_utils_end
    
    extern function new(string name = "i2c_timings");

endclass // i2c_timings

//-------------------------------------------------------------------------------------------------------------
function i2c_timings::new(string name = "i2c_timings");
    super.new(name);
endfunction // new


