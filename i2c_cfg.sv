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

//  Driver configuration
    protected int period_SM = 10000;  // ns
    protected int period_FM = 2500;
    protected int period_FMP = 1000;
    protected int period_HSM = 300;   // not exact value, a bit higher for simulation purposes 
    
    rand speed_mode_enum default_speed_mode;
    /*static?*/ rand speed_mode_enum speed_mode;

//  Simulation timeout
    time test_time_out = 100000000;

//  Default constraints 
    constraint i2c_cfg_default_cst {        
        soft has_coverage == 1;
        soft has_checks == 1;
        soft default_speed_mode == SM;
             speed_mode == default_speed_mode;
    }
//------------------------------------------------------------------------------------------------------------
// Shorthand macros
//------------------------------------------------------------------------------------------------------------
    `uvm_object_utils_begin(i2c_cfg)
        `uvm_field_int (has_coverage, UVM_ALL_ON)
        `uvm_field_int (has_checks, UVM_ALL_ON)
    `uvm_object_utils_end
    
    extern function new(string name = "i2c_cfg");
    extern function int get_delay(period_fraction_enum period_fraction = QUARTER);

endclass // i2c_cfg

//-------------------------------------------------------------------------------------------------------------
function i2c_cfg:: new(string name = "i2c_cfg");
    super.new(name);
endfunction // new

function int i2c_cfg:: get_delay(period_fraction_enum period_fraction = QUARTER);
  int period;
  case (speed_mode)
    SM:   period = period_SM;
    FM:   period = period_FM;
    FMP:  period = period_FMP;
    HSM:  period = period_HSM;
  endcase
  case (period_fraction)
    FULL:     return period;
    HALF:     return period/2;
    QUARTER:  return period/4;
    QUANTUM:  return period/20;
  endcase
endfunction


