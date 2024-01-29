class i2c_cfg extends uvm_object;
  `uvm_object_utils(i2c_cfg)

  // *** Environment configuration parameters ***
  rand bit high_speed_only; //Enables high speed mode only
  rand bit has_coverage; //Enables coverage  
  rand agent_type_enum agent_type; // master (0) or slave (1)
  
  // *** Agent configuration parameters ***
  rand slave_driver_type_enum slave_driver_type; // peripheral device (0) or polling CPU (1)

  rand speed_mode_enum default_speed_mode;
  rand speed_mode_enum higher_speed_mode;

  // *** Data sharing parameters ***
  rand speed_mode_enum current_speed_mode;
  uvm_event master_finish;
    
  //Simulation timeout
  time test_time_out = 64'd0000000000;

  constraint c_cfg {
    current_speed_mode == default_speed_mode;
    periods[default_speed_mode] > periods[higher_speed_mode];
  }

  //Default constraints 
  constraint c_cfg_defaults {    
    soft high_speed_only == 0;  
    soft has_coverage == 1;
    soft default_speed_mode == SM;
    soft higher_speed_mode == FMP;
    soft slave_driver_type == PERIPHERAL_DEVICE;
  }
    
  extern function new(string name = "i2c_cfg");
  extern function time get_delay(period_fraction_enum fraction = QUARTER);
  extern function void toggle_speed_mode();
  extern function void reset_speed_mode();
endclass // i2c_cfg

//-------------------------------------------------------------------------------------------------------------
function i2c_cfg:: new(string name = "i2c_cfg");
  super.new(name);
  master_finish = new("master_finish");
endfunction // i2c_cfg::new

// Returns the delay for the current speed mode
// fraction: FULL, HALF, QUARTER, QUANTUM (1/20th of a period)
function time i2c_cfg:: get_delay(period_fraction_enum fraction = QUARTER);
  time period = periods[current_speed_mode];
  case (fraction)
    FULL:     return period;
    HALF:     return period/2;
    QUARTER:  return period/4;
    QUANTUM:  return period/20;
  endcase
endfunction // i2c_cfg::get_delay

// Toggles the speed mode between default and higher
// Updates the config_db cfg
function void i2c_cfg:: toggle_speed_mode();
  if (current_speed_mode == default_speed_mode)
    current_speed_mode = higher_speed_mode;
  else if (current_speed_mode == higher_speed_mode)
    current_speed_mode = default_speed_mode;
  else
    `uvm_fatal("i2c_cfg", "Unknown speed mode");

  uvm_config_db#(speed_mode_enum)::set(null, "uvm_test_top.*.s_drv.cfg", "current_speed_mode", current_speed_mode);
  uvm_config_db#(speed_mode_enum)::set(null, "uvm_test_top.*.m_drv.cfg", "current_speed_mode", current_speed_mode);
endfunction // i2c_cfg::toggle_speed_mode

// Resets the speed mode to default
// Updates the config_db cfg
function void i2c_cfg:: reset_speed_mode();
  current_speed_mode = default_speed_mode;
  uvm_config_db#(speed_mode_enum)::set(null, "uvm_test_top.*.s_drv.cfg", "current_speed_mode", current_speed_mode);
  uvm_config_db#(speed_mode_enum)::set(null, "uvm_test_top.*.m_drv.cfg", "current_speed_mode", current_speed_mode);
endfunction // i2c_cfg::reset_speed_mode