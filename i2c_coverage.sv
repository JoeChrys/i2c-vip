/*
      * * * Coverage class, fill your specific coverpoints down bellow * * *
*/


class i2c_coverage extends uvm_component;
	`uvm_component_param_utils(i2c_coverage)
	
    i2c_cfg cfg; 
    
    covergroup i2c_end_state_with_start_stop with function sample(
        i2c_item item,
        scoreboard_state_enum state
      );
      
      // * * * * WRITE YOUR COVERPOINTS HERE * * * * 
      each_state_start_stop: cross item.start_condition, item.stop_condition, state{
        ignore_bins no_stop_expected = each_state_start_stop with (
          item.stop_condition == 0 && state == WAIT_FOR_START || DEVICE_ID_WRITE
        );
        ignore_bins both_start_stop = each_state_start_stop with (
          (item.start_condition == 1 && item.stop_condition == 1) || 
          (item.start_condition == 0 && item.stop_condition == 0)
        );
      }
    endgroup

    covergroup i2c_addresses with function sample(
        scoreboard_state_enum state
      );
      
      coverpoint state {
        bins basic_states[] = {WAIT_FOR_START, ADDRESSING};
        bins all_states[] = {NORMAL_WRITE, NORMAL_READ,
        GENERAL_CALL_STATE, CBUS_STATE, OTHER_BUS_STATE, FUTURE_PURPOSE_STATE,
        DEVICE_ID_WRITE, DEVICE_ID_READ, TEN_BIT_ADDR_WRITE, TEN_BIT_ADDR_READ};

        bins state_transitions[] = { ADDRESSING -> all_states}
        bins normal_write = {ADDRESSING -> NORMAL_WRITE};
        bins normal_read = {ADDRESSING -> NORMAL_WRITE -> ADDRESSING -> NORMAL_READ};
        bins general_call = {ADDRESSING -> GENERAL_CALL_STATE};
        bins cbus = {ADDRESSING -> CBUS_STATE};
        bins other_buses = {ADDRESSING -> OTHER_BUS_STATE};
        bins future_purpose = {ADDRESSING -> FUTURE_PURPOSE_STATE};
        bins device_id_write = {ADDRESSING -> DEVICE_ID_WRITE -> ADDRESSING -> DEVICE_ID_READ};
        bins ten_bit_addr_write = {ADDRESSING -> TEN_BIT_ADDR_WRITE};
        bins ten_bit_addr_read = {ADDRESSING -> TEN_BIT_ADDR_WRITE -> ADDRESSING -> TEN_BIT_ADDR_READ};
      }
    endgroup

    // covergroup for bus busy?
	
    extern function new(string name = "i2c_coverage", uvm_component parent);
    extern virtual function void build_phase(uvm_phase phase);
endclass

function i2c_coverage::new(string name = "i2c_coverage", uvm_component parent);
    super.new(name, parent);
    i2c_cg = new();	
endfunction // i2c_coverage::new

function void  i2c_coverage::build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg))   
        `uvm_fatal("build_phase", "cfg wasn't set through config db");
endfunction // i2c_coverage::build_phase

