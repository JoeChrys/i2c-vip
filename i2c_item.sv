
class i2c_item#(int ADDR = 32, int DATA = 32) extends uvm_sequence_item; 
    
// * * * Add fields bellow * * *
rand bit[8] data;
rand bit ack;

// * * * Add constraints * * *
constraint ack_bit_1 {ack == 1;}

//-------------------------------------------------------------------
// Shorthand macros
//-------------------------------------------------------------------

// * * * Register variables in factory * * * 
    `uvm_object_utils_begin(i2c_item) 

    `uvm_object_utils_end
    extern function new(string name = "i2c_item");
endclass // i2c_item

function i2c_item::new(string name = "i2c_item");
    super.new(name);
endfunction 

