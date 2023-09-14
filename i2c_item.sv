
class i2c_item extends uvm_sequence_item; 
    
// * * * Add fields bellow * * *
rand bit[7:0] data [];
rand bit ack_nack;

rand transaction_type_enum transaction_type;

rand bit start_condition;
rand bit stop_condition;

rand integer delay;
rand integer clock_stretch;

// * * * Add constraints * * *
constraint c_ack { soft ack_nack == `NACK; } // can remove "soft"

constraint c_delay { delay inside {[0:10]}; soft delay == 0; }
constraint c_clock_stretch { clock_stretch inside {[0:10]}; soft clock_stretch == 0; }

constraint c_start_stop { soft start_condition == 0; soft stop_condition == 0; }

constraint c_data_size { soft data.size() == 1; }

constraint c_write_transaction { soft transaction_type == WRITE; }
constraint c_read_transaction { if (transaction_type == READ) { start_condition == 0 }; }

//-------------------------------------------------------------------
// Shorthand macros
//-------------------------------------------------------------------

// * * * Register variables in factory * * * 
    `uvm_object_utils_begin(i2c_item) 
        `uvm_field_array_int(data, UVM_DEFAULT|UVM_HEX)
        `uvm_field_int(ack_nack, UVM_DEFAULT|UVM_BIN)
        `uvm_field_enum(transaction_type_enum, transaction_type, UVM_DEFAULT)
        `uvm_field_int(start_condition, UVM_DEFAULT|UVM_BIN)
        `uvm_field_int(stop_condition, UVM_DEFAULT|UVM_BIN)
        `uvm_field_int(delay, UVM_DEFAULT)
        `uvm_field_int(clock_stretch, UVM_DEFAULT)
    `uvm_object_utils_end


    extern function new(string name = "i2c_item");
endclass // i2c_item

function i2c_item::new(string name = "i2c_item");
    super.new(name);
endfunction 

