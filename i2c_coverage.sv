/*
      * * * Coverage class, fill your specific coverpoints down bellow * * *
*/


class i2c_coverage extends uvm_component;
	`uvm_component_param_utils(i2c_coverage)
	
    i2c_cfg cfg; 

    covergroup i2c_addresses with function sample(
        i2c_item item,
        scoreboard_state_enum state
      );
      
      coverpoint state {
        bins basic_states[] = {WAIT_FOR_START, ADDRESSING};
        bins all_states[] = {NORMAL_WRITE, NORMAL_READ,
        GENERAL_CALL_STATE, CBUS_STATE, OTHER_BUS_STATE, FUTURE_PURPOSE_STATE,
        DEVICE_ID_WRITE, DEVICE_ID_READ, TEN_BIT_ADDR_WRITE, TEN_BIT_ADDR_READ};

        // bins state_transitions[] = { ADDRESSING -> all_states};
        bins normal_write = (ADDRESSING => NORMAL_WRITE);
        bins normal_read = (ADDRESSING => NORMAL_WRITE => ADDRESSING => NORMAL_READ);
        bins general_call = (ADDRESSING => GENERAL_CALL_STATE);
        bins cbus = (ADDRESSING => CBUS_STATE);
        bins other_buses = (ADDRESSING => OTHER_BUS_STATE);
        bins future_purpose = (ADDRESSING => FUTURE_PURPOSE_STATE);
        bins device_id_write = (ADDRESSING => DEVICE_ID_WRITE => ADDRESSING => DEVICE_ID_READ);
        bins ten_bit_addr_write = (ADDRESSING => TEN_BIT_ADDR_WRITE);
        bins ten_bit_addr_read = (ADDRESSING => TEN_BIT_ADDR_WRITE => ADDRESSING => TEN_BIT_ADDR_READ);
      }

      coverpoint item.data[7:1] {
        // bins ten_bit_addr[4] = {[7'b111_1000:7'b111_1011]};
        bins c_bus = {C_BUS};
        bins other_buses = {OTHER_BUSES};
        bins future_purpose = {FUTURE_PURPOSE};

        bins speed_mode = {[{SPEED_MODE,2'b00}:{SPEED_MODE,2'b11}]};
        bins device_id = {[{DEVICE_ID,2'b00}:{DEVICE_ID,2'b11}]};

        bins ten_bit_addr[4] = {[{TEN_BIT_TARGET_ADDRESSING,2'b00}:{TEN_BIT_TARGET_ADDRESSING,2'b11}]};
      }

      coverpoint item.data {
        bins general_call = {GENERAL_CALL};
        bins start_byte = {START_BYTE};
      }
    endgroup

    covergroup i2c_end_state_with_start_stop with function sample(
        i2c_item item,
        scoreboard_state_enum state
      );
      
      cp_start_condition: coverpoint item.start_condition;
      cp_stop_condition: coverpoint item.stop_condition;
      cp_state: coverpoint state;

      each_state_start_stop: cross cp_start_condition, cp_stop_condition, cp_state {
        // Ignore bins
        ignore_bins ignore_WAIT_FOR_START = binsof(cp_state) intersect {WAIT_FOR_START} && binsof(cp_stop_condition) intersect {0};
        ignore_bins ignore_DEVICE_ID_WRITE = binsof(cp_state) intersect {DEVICE_ID_WRITE} && binsof(cp_stop_condition) intersect {0};
        ignore_bins ignore_start_stop = binsof(cp_start_condition) intersect {1} && binsof(cp_stop_condition) intersect {1};
      }
    endgroup
	
    extern function new(string name = "i2c_coverage", uvm_component parent);
    extern virtual function void build_phase(uvm_phase phase);
endclass

function i2c_coverage::new(string name = "i2c_coverage", uvm_component parent);
    super.new(name, parent);
    i2c_end_state_with_start_stop = new();
    i2c_addresses = new();
endfunction // i2c_coverage::new

function void  i2c_coverage::build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg))   
        `uvm_fatal("build_phase", "cfg wasn't set through config db");
endfunction // i2c_coverage::build_phase

