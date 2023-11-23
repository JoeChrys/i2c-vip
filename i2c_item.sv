
class i2c_item extends uvm_sequence_item; 
    
// Interface fields
rand bit[7:0]                 data;
rand bit                      ack_nack;

// Master Driver fields
rand bit                      start_condition;
rand bit                      stop_condition;
rand int                      delay;

// Slave Driver fields
rand int                      clock_stretch_data[7:0];
rand int                      clock_stretch_ack;

// REQ/RSP fields
rand transaction_type_enum    transaction_type;
rand bit                      transfer_failed;

// Default/Universal Constraints
constraint c_ack                { soft (ack_nack == `ACK); }

constraint c_delay              { delay >= 0;
                                  soft (delay == 0); }

constraint c_clock_stretch_ack  { clock_stretch_ack >= 0;
                                  soft (clock_stretch_ack == 0); }

constraint c_clock_stretch_data { foreach (clock_stretch_data[i]) {
                                    clock_stretch_data[i] >= 0;
                                    soft (clock_stretch_data[i] == 0); } }

constraint c_start_stop         { soft (start_condition == 0);
                                  soft (stop_condition == 0); }

constraint c_read_transaction   { if (transaction_type == READ) {
                                    start_condition == 0;
                                    stop_condition == 0; } }

// ! how to handle multiple drivers
// constraint c_transfer_failed    { soft transfer_failed == 'b0; 
//                                   if (transfer_failed) { delay == 0; } }

//-------------------------------------------------------------------
// Shorthand macros
//-------------------------------------------------------------------

// * * * Register variables in factory * * * 
    `uvm_object_utils_begin(i2c_item) 
        `uvm_field_int(data, UVM_DEFAULT|UVM_HEX)
        `uvm_field_int(ack_nack, UVM_DEFAULT|UVM_BIN)
        `uvm_field_int(start_condition, UVM_DEFAULT|UVM_BIN)
        `uvm_field_int(stop_condition, UVM_DEFAULT|UVM_BIN)
        `uvm_field_int(delay, UVM_DEFAULT)
        `uvm_field_sarray_int(clock_stretch_data, UVM_DEFAULT)
        `uvm_field_int(clock_stretch_ack, UVM_DEFAULT)
        `uvm_field_enum(transaction_type_enum, transaction_type, UVM_DEFAULT)
        `uvm_field_int(transfer_failed, UVM_DEFAULT|UVM_BIN)
    `uvm_object_utils_end


    extern function new(string name = "i2c_item");
endclass // i2c_item

function i2c_item:: new(string name = "i2c_item");
    super.new(name);
endfunction 

