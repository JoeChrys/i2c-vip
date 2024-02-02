class i2c_delay_and_clock_stretch_test extends i2c_basic_test;
  `uvm_component_utils(i2c_delay_and_clock_stretch_test)

  i2c_master_start_byte m_start_byte;
  i2c_master_high_speed_mode m_high_speed_mode;
      
  extern function new(string name = "i2c_delay_and_clock_stretch_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
endclass // i2c_delay_and_clock_stretch_test

//-------------------------------------------------------------------------------------------------------------
function i2c_delay_and_clock_stretch_test:: new(string name = "i2c_delay_and_clock_stretch_test", uvm_component parent=null);    
  super.new(name,parent);
endfunction // new

//-------------------------------------------------------------------------------------------------------------
function void i2c_delay_and_clock_stretch_test:: build_phase(uvm_phase phase);
  
  set_type_override_by_type(i2c_virtual_write_with_stop_no_delays_no_cs::get_type(), i2c_virtual_write_with_stop_with_delays_with_cs_all::get_type());
  set_type_override_by_type(i2c_virtual_read_with_stop_no_delays_no_cs::get_type(), i2c_virtual_read_with_stop_with_delays_with_cs_all::get_type());
  set_type_override_by_type(i2c_virtual_write_no_stop_no_delays_no_cs::get_type(), i2c_virtual_write_no_stop_with_delays_with_cs_all::get_type());
  set_type_override_by_type(i2c_virtual_read_no_stop_no_delays_no_cs::get_type(), i2c_virtual_read_no_stop_with_delays_with_cs_all::get_type());
    
  super.build_phase(phase);
endfunction // build_phase

function void i2c_delay_and_clock_stretch_test:: start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
endfunction // start_of_simulation_phase