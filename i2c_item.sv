
class i2c_item extends uvm_sequence_item; 
    
// * * * Add fields bellow * * *
rand bit[7:0] data;
rand ack_nack_enum response;

rand item_type_enum com_type;

rand integer delay;
rand integer clock_stretch;

// * * * Add constraints * * *
constraint c_ack {soft response == NACK;}

constraint c_delay {delay inside {[0:10]}; soft delay == 0;}
constraint c_clock_stretch {clock_stretch inside {[0:10]}; soft clock_stretch == 0;}

constraint c_com_type {soft com_type == DATA;}

//-------------------------------------------------------------------
// Shorthand macros
//-------------------------------------------------------------------

// * * * Register variables in factory * * * 
    `uvm_object_utils_begin(i2c_item) 
        `uvm_field_int(data, UVM_DEFAULT|UVM_HEX)
        //`uvm_field_int(ack, UVM_DEFAULT|UVM_BIN)
        // TODO Add the rest of the variables
    `uvm_object_utils_end


    extern function new(string name = "i2c_item");
endclass // i2c_item

function i2c_item::new(string name = "i2c_item");
    super.new(name);
endfunction 

