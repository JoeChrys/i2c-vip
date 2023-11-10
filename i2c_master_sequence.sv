class i2c_master_base_sequence extends uvm_sequence #(i2c_item);
 
  `uvm_object_utils(i2c_master_base_sequence)
  `uvm_declare_p_sequencer(i2c_master_sequencer)
  
  i2c_cfg cfg;

  rand bit transfer_failed;
  rand bit stop_on_nack;
  rand bit stop_on_fail;

  // Item fields for Master Seq
  rand transaction_type_enum  transaction_type;
  rand bit[7:0]               data;
  rand bit                    ack_nack;
  rand bit                    start_condition;
  rand bit                    stop_condition;
  rand int                    delay;

  constraint c_master_transfer_failed {
    soft (transfer_failed == 0); 
  }
  constraint c_master_stop_on {
    soft (stop_on_nack == 1);
    soft (stop_on_fail == 0); 
  }
  constraint c_master_transaction_type {
    soft (transaction_type == WRITE); 
  }
  constraint c_master_conditions {
    soft (start_condition == 0);
    soft (stop_condition == 0); 
  }
  constraint c_master_delay { 
    soft (delay == 0); 
  }
  
  extern function new(string name = "i2c_master_base_sequence");
  extern virtual task body();
  extern virtual function void post_do(uvm_sequence_item this_item);

endclass // i2c_master_sequence

//-------------------------------------------------------------------
function i2c_master_base_sequence:: new(string name = "i2c_master_base_sequence");
    super.new(name);
endfunction // i2c_sequence::new

//-------------------------------------------------------------------
task i2c_master_base_sequence:: body();
  
  // TODO add below to pre_start()
  uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
  if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg",cfg))
      `uvm_fatal("Master Sequence", "cfg wasn't set through config db");

// * * * `uvm_do or `uvm_do_with can be used here * * * 
  // `uvm_do_with(req, { 
  //     transaction_type == local::transaction_type;
  //     data == local::data;
  //     ack_nack == local::ack_nack;
  //     start_condition == local::start_condition;
  //     stop_condition == local::stop_condition;
  //     delay == local::delay;
  //     })
  req = i2c_item::type_id::create("req");
  start_item(req);
  if ( !req.randomize() with { 
    transaction_type == local::transaction_type;
    data == local::data;
    ack_nack == local::ack_nack;
    start_condition == local::start_condition;
    stop_condition == local::stop_condition;
    delay == local::delay;
    } )
    `uvm_error("MASTER SEQ", "Sequence Randomization failed")
  finish_item(req);

  `uvm_info("MASTER SEQ", "WAITING FOR RSP", UVM_DEBUG)
  get_response(rsp);
  `uvm_info("MASTER SEQ", "GOT RSP", UVM_DEBUG)
  // transfer_failed = rsp.transfer_failed;
  // if (transaction_type == WRITE) begin
  //   ack_nack = rsp.ack_nack;
  // end

endtask

function void i2c_master_base_sequence:: post_do(uvm_sequence_item this_item);
  `uvm_info(get_type_name(), "post_do called", UVM_DEBUG)
  i2c_item rsp;
  $cast(rsp, this_item);

  transfer_failed |= rsp.transfer_failed;
  if (transfer_failed) begin
    `uvm_error("MASTER SEQ" "RSP indicates failed seq")
    if (stop_on_fail) begin
      disable body;
    end
  end
  if (stop_on_nack) begin
    if (rsp.ack_nack == `NACK) begin
      `uvm_info("MASTER SEQ", "Got NACK, stoping current sequence", UVM_LOW)
      disable body;
    end 
  end
endfunction

class i2c_master_multibyte_sequence extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_multibyte_sequence)
  // `uvm_declare_p_sequencer(i2c_master_sequencer)

  i2c_master_base_sequence    seq;
  rand int                    number_of_bytes;

  // Item fields for Master Seq
  rand bit[7:0]               data[];
  rand bit                    ack_nack[];
  rand int                    delay[];

  constraint c_master_mb_nob {
    number_of_bytes > 0;
    soft (number_of_bytes < 20); 
  }
  constraint c_master_mb_array_size {
    data.size() == number_of_bytes;
    ack_nack.size() == number_of_bytes;
    delay.size() == number_of_bytes; 
  }
  constraint c_master_mb_delay {
    foreach(delay[i]) { 
      delay[i] >= 0; 
      soft (delay[i] == 0);
    }
  }
  
  extern function new(string name = "i2c_master_multibyte_sequence");
  extern virtual task body();

endclass // i2c_master_multibyte_sequence

//-------------------------------------------------------------------
function i2c_master_multibyte_sequence:: new(string name = "i2c_master_multibyte_sequence");
    super.new(name);
endfunction //i2c_sequence::new

//-------------------------------------------------------------------
task i2c_master_multibyte_sequence:: body();
  seq = i2c_master_base_sequence::type_id::create("seq");

  for ( int i = 0; i < number_of_bytes; i++) begin
    if ( !seq.randomize() with { 
      transaction_type == local::transaction_type;
      data == local::data[i];
      ack_nack == local::ack_nack[i];
      if (local::i == 0)                  {start_condition == local::start_condition;}
      if (local::i == number_of_bytes-1)  {stop_condition == local::stop_condition;}
      delay == local::delay;
    } ) 
      `uvm_error("Master Sequence", $sformatf("Multibyte Sequence Randomization failed at %0d", i))
    seq.start(p_sequencer, this);
  end

endtask 

class i2c_master_write_sequence extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_write_sequence)

  i2c_master_base_sequence    seq;

  rand int                    number_of_bytes;
  rand bit                    ignore_register;

  // Item fields for Master Seq
  rand bit[7:0]               target_address;
  rand bit[7:1]               register_address;
  rand bit                    stop_condition;
  rand bit[7:0]               data[];
  rand int                    delay[];

  constraint c_master_write_nob {
    number_of_bytes > 0;
    soft (number_of_bytes < 20); 
  }
  constraint c_master_write_array_size {
    data.size() == number_of_bytes;
    delay.size() == number_of_bytes+2; 
  }
  constraint c_master_write_delay {
    foreach(delay[i]) { 
      delay[i] >= 0; 
      soft (delay[i] == 0); 
    }
  }
  constraint c_master_write_ignore_reg {
    soft (ignore_register == 'b0); 
  }
  
  extern function new(string name = "i2c_master_write_sequence");
  extern virtual task body();

endclass // i2c_master_write_sequence

//-------------------------------------------------------------------
function i2c_master_write_sequence:: new(string name = "i2c_master_write_sequence");
    super.new(name);
endfunction // i2c_master_write_sequence::new

//-------------------------------------------------------------------
task i2c_master_write_sequence:: body();

  seq = i2c_master_base_sequence::type_id::create("seq");

  // Send target address
  if ( !seq.randomize() with { 
    transaction_type == WRITE;
    start_condition == 'b1;
    data == { target_address, `W };
    delay == local::delay[0];
    } )
  `uvm_error("Master Sequence", "Write Sequence Randomization failed at Target Adress")
  seq.start(p_sequencer, this);
  

  // Send register address
  if (!ignore_register) begin
    if ( !seq.randomize() with { 
      transaction_type == WRITE;
      data == register_address;
      delay == local::delay[1];
      } )
    `uvm_error("Master Sequence", "Write Sequence Randomization failed at Register Address")
    seq.start(p_sequencer, this);
  end

  for ( int i = 0; i < number_of_bytes; i++) begin
    if ( !seq.randomize() with { 
      transaction_type == WRITE;
      data == local::data[i];
      if (local::i == number_of_bytes-1)  {stop_condition == local::stop_condition;}
      delay == local::delay[i+2];
      } )
      `uvm_error("Master Sequence", $sformatf("Write Sequence Randomization failed at %3d", i))
    seq.start(p_sequencer, this);
    
  end

endtask 

class i2c_master_read_sequence extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_read_sequence)

  i2c_master_base_sequence    seq;
  rand int                    number_of_bytes;
  rand bit                    ignore_register;

  // Item fields for Master Seq
  rand bit[7:0]               target_address;
  rand bit[7:1]               register_address;
  rand bit                    stop_condition;
  rand bit[7:0]               ack_nack[];
  rand int                    delay[];

  constraint c_master_read_nob {
    number_of_bytes > 0;
    soft (number_of_bytes < 20); 
  }
  constraint c_master_read_array_size {
    ack_nack.size() == number_of_bytes;
    delay.size() == number_of_bytes+3; 
  }
  constraint c_master_read_delay {
    foreach(delay[i]) { 
      delay[i] >= 0; 
      soft (delay[i] == 0); 
    } 
  }
  constraint c_master_write_ignore_reg {
    soft (ignore_register == 'b0);
  }
  
  extern function new(string name = "i2c_master_read_sequence");
  extern virtual task body();

endclass // i2c_master_read_sequence

//-------------------------------------------------------------------
function i2c_master_read_sequence:: new(string name = "i2c_master_read_sequence");
    super.new(name);
endfunction //i2c_sequence::new

//-------------------------------------------------------------------
task i2c_master_read_sequence:: body();

  seq = i2c_master_base_sequence::type_id::create("seq");

  // Send target address
  if ( !seq.randomize() with { 
    transaction_type == WRITE;
    start_condition == 'b1;
    data == { target_address, `W };
    delay == local::delay[0];
    } )
  `uvm_error("Master Sequence", "Read Sequence Randomization failed at Target Adress")
  seq.start(p_sequencer, this);
  

  // Send register address
  if (!ignore_register) begin
    if ( !seq.randomize() with { 
      transaction_type == WRITE;
      data == register_address;
      delay == local::delay[1];
      } )
    `uvm_error("Master Sequence", "Read Sequence Randomization failed at Register Address")
    seq.start(p_sequencer, this);
  end

  // Send target address again (read)
  if ( !seq.randomize() with { 
    transaction_type == WRITE;
    start_condition == 'b1;
    data == { target_address, `R };
    delay == local::delay[2];
    } )
  `uvm_error("Master Sequence", "Read Sequence Randomization failed at Target Adress")
  seq.start(p_sequencer, this);
  

  for ( int i = 0; i < number_of_bytes; i++) begin
    if ( !seq.randomize() with { 
      transaction_type == READ;
      if (local::i == number_of_bytes-1)  {stop_condition == local::stop_condition;}
      delay == local::delay[i+2];
      } )
      `uvm_error("Master Sequence", $sformatf("Read Sequence Randomization failed at %3d", i))
    seq.start(p_sequencer, this);
    
  end

endtask 