class i2c_master_base_sequence extends uvm_sequence #(i2c_item);
  `uvm_object_utils(i2c_master_base_sequence)
  `uvm_declare_p_sequencer(i2c_master_sequencer)
  
  i2c_cfg cfg;

  rand bit transfer_failed;
  rand bit receiver_response;
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
  constraint c_master_receiver_response {
    soft (receiver_response == `ACK);
  }
  constraint c_master_stop_on {
    soft (stop_on_nack == 1);
    soft (stop_on_fail == 0); 
  }
  constraint c_master_transaction_type {
    soft (transaction_type == WRITE); 
  }
  constraint c_master_ack_nack {
    soft (ack_nack == `ACK);
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
  extern virtual function int check_exit();
endclass // i2c_master_sequence

//-------------------------------------------------------------------
function i2c_master_base_sequence:: new(string name = "i2c_master_base_sequence");
  super.new(name);
endfunction // i2c_sequence::new

//-------------------------------------------------------------------
task i2c_master_base_sequence:: body();
  
  uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
  if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg",cfg))
    `uvm_fatal("Master Sequence", "cfg wasn't set through config db");

  req = i2c_item::type_id::create("req");
  start_item(req);
  if ( !req.randomize() with { 
      transaction_type == local::transaction_type;
      data == local::data;
      ack_nack == local::ack_nack;
      start_condition == local::start_condition;
      stop_condition == local::stop_condition;
      delay == local::delay;
    }
  ) `uvm_error(get_type_name(), "Sequence Randomization failed")
  finish_item(req);

  get_response(rsp);
  transfer_failed = rsp.transfer_failed;
  if (transaction_type == WRITE) begin
    receiver_response = rsp.ack_nack;
  end

endtask

function int i2c_master_base_sequence:: check_exit();
  if (transfer_failed) begin
    `uvm_error("SEQFAIL", "Response from REQ indicates failure")
    return 1;
  end
  if (receiver_response == `NACK) begin
    `uvm_info(get_type_name(), "Got NACK from slave", UVM_LOW)
    return 2;
  end
  return 0;
endfunction
