/*
* * * * *   AGENT CONFIGURATION     * * * * * 
    You can add specific fields for your agents here
*/

class i2c_cfg extends uvm_object;  

//  Enables protocol checks
    rand bit has_checks;
    rand bit ready_high;
//  Enables coverage  
    rand bit has_coverage;
    rand agent_type_enum agent_type; // master (0) or slave (1)


//  Simulation timeout
    time test_time_out = 100000000;

//  Default constraints 
    constraint i2c_cfg_default_cst {        
        soft has_coverage == 1;
        soft has_checks == 1;
    }
//------------------------------------------------------------------------------------------------------------
// Shorthand macros
//------------------------------------------------------------------------------------------------------------
    `uvm_object_utils_begin(i2c_cfg)
        `uvm_field_int (has_coverage, UVM_ALL_ON)
        `uvm_field_int (has_checks, UVM_ALL_ON)
    `uvm_object_utils_end
    
    extern function new(string name = "i2c_cfg");

endclass // i2c_cfg

//-------------------------------------------------------------------------------------------------------------
function i2c_cfg::new(string name = "i2c_cfg");
    super.new(name);
endfunction // new


