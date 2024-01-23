
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
  constraint c_ack  { 
    soft (ack_nack == `ACK); 
  }

  constraint c_delay { 
    delay >= 0;
    soft (delay == 0); 
  }

  constraint c_clock_stretch_ack {
    clock_stretch_ack >= 0;
    soft (clock_stretch_ack == 0);
  }

  constraint c_clock_stretch_data { 
    foreach (clock_stretch_data[i]) {
      clock_stretch_data[i] >= 0;
      soft (clock_stretch_data[i] == 0);
    }
  }

  constraint c_start_stop { 
    soft (start_condition == 0);
    soft (stop_condition == 0);
  }

  constraint c_read_transaction { 
    if (transaction_type == READ) {start_condition == 0;}
  }

  extern function new(string name = "i2c_item");
endclass // i2c_item

function i2c_item:: new(string name = "i2c_item");
  super.new(name);
endfunction // i2c_item::new

