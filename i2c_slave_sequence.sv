
class i2c_slave_base_sequence extends uvm_sequence #(i2c_item);
  `uvm_object_utils(i2c_slave_base_sequence)
  `uvm_declare_p_sequencer(i2c_slave_sequencer)

  // static uvm_event_pool ev_pool = uvm_event_pool:: get_global_pool();
  // static uvm_event seq_finished;

  i2c_cfg cfg;

  rand bit transfer_failed;
  rand bit receiver_response;
  rand bit stop_on_nack;
  rand bit stop_on_fail;

  // *** Item fields for Slave Seq ***
  rand transaction_type_enum  transaction_type;
  rand bit[7:0]               data;
  rand bit                    ack_nack;
  rand int                    clock_stretch_data[7:0];
  rand int                    clock_stretch_ack;

  // *** Constraints for Slave Seq ***
  constraint c_slave_transfer_failed {
    soft (transfer_failed == 0);
  }
  constraint c_slave_receiver_response {
    soft (receiver_response == `ACK);
  }
  constraint c_slave_stop_on {
    soft (stop_on_nack == 1);
    soft (stop_on_fail == 0);
  }
  constraint c_slave_transaction_type {
    soft (transaction_type == READ); 
  }
  constraint c_slave_clock_stretch {
    soft (clock_stretch_ack == 0);
    foreach (clock_stretch_data[i]) {
      soft (clock_stretch_data[i] == 0);
    }
  }

  extern function new(string name = "i2c_slave_base_sequence");
  extern virtual task body();
  extern local virtual task pre_start();
  extern local virtual task post_start();
  extern local virtual function int check_exit(bit stop_on_fail, bit stop_on_nack);
endclass // i2c_slave_base_sequence

//-------------------------------------------------------------------
function i2c_slave_base_sequence:: new(string name = "i2c_slave_base_sequence");
    super.new(name);
endfunction //i2c_sequence::new

//-------------------------------------------------------------------
task i2c_slave_base_sequence:: body();
    
  // TODO add below to pre_start()
  // uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
  // if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg",cfg))
  //     `uvm_fatal("body", "cfg wasn't set through config db");

// * * * uvm_do or uvm_do_with can be used * * * 
  // `uvm_do_with(req, { 
  //     transaction_type == local::transaction_type; 
  //     data == local::data;
  //     ack_nack == local::ack_nack;
  //     foreach (local::clock_stretch_data[i]) 
  //         {clock_stretch_data[i] == local::clock_stretch_data[i]};
  //     clock_stretch_ack == local::clock_stretch_ack;
  //     })
  req = i2c_item::type_id::create("req");
  start_item(req);
  if ( !req.randomize() with { 
      transaction_type == local::transaction_type; 
      data == local::data;
      ack_nack == local::ack_nack;
      clock_stretch_ack == local::clock_stretch_ack;
      foreach (local::clock_stretch_data[i]) {
        clock_stretch_data[i] == local::clock_stretch_data[i];
      }
    }
  ) `uvm_error("SLAVE SEQ", "Sequence Randomization failed")
  finish_item(req);

  `uvm_info("SLAVE SEQ", "WAITING FOR RSP", UVM_DEBUG)
  get_response(rsp);
  `uvm_info("SLAVE SEQ", "GOT RSP", UVM_DEBUG)
  transfer_failed = rsp.transfer_failed;
  if (transaction_type == WRITE) begin
    receiver_response = rsp.ack_nack;
  end

endtask

task i2c_slave_base_sequence:: pre_start();
  `uvm_info(get_type_name(), "PRE START", UVM_DEBUG)
  // seq_finished = ev_pool.get($sformatf("%m"));

  uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
  if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg",cfg))
      `uvm_fatal("body", "cfg wasn't set through config db");
endtask

task i2c_slave_base_sequence:: post_start();
  `uvm_info(get_type_name(), "POST START", UVM_DEBUG)
  // fork
    // seq_finished.trigger();
  // join_none
endtask

function int i2c_slave_base_sequence:: check_exit(bit stop_on_fail, bit stop_on_nack);
  if (transfer_failed) begin
    `uvm_error("SEQFAIL", "Response from REQ indicates failure")
    if (stop_on_fail) return 1;
  end
  if (receiver_response == `NACK) begin
    `uvm_info("SLAVESEQ", "Got NACK", UVM_HIGH)
    if (stop_on_nack) return 2;
  end
  return 0;
endfunction

class i2c_slave_multibyte_sequence extends i2c_slave_base_sequence;
  `uvm_object_utils(i2c_slave_multibyte_sequence)

  i2c_slave_base_sequence   seq;
  rand int                  number_of_bytes;

  // Item fields for Slave Seq
  rand bit[7:0]         data[];
  rand bit              ack_nack[];
  rand int              clock_stretch_data[][8];
  rand int              clock_stretch_ack[];

  constraint c_slave_mb_nob { 
    number_of_bytes > 0;
    soft (number_of_bytes < 20); 
  }
  constraint c_slave_mb_array_size {
    data.size() == number_of_bytes;
    ack_nack.size() == number_of_bytes;
    clock_stretch_data.size() == number_of_bytes;
    clock_stretch_ack.size() == number_of_bytes; 
  }
  constraint c_slave_mb_clock_stretch_data  {
    foreach (clock_stretch_data[i]) {
      foreach (clock_stretch_data[i][j]) {
        clock_stretch_data[i][j] >= 0;
        soft (clock_stretch_data[i][j] == 0);
      }
    } 
  }

  extern function new(string name = "i2c_slave_multibyte_sequence");
  extern virtual task body();

endclass // i2c_slave_multibyte_sequence

function i2c_slave_multibyte_sequence:: new(string name = "i2c_slave_multibyte_sequence");
  super.new(name);
endfunction

task i2c_slave_multibyte_sequence:: body();
  seq = i2c_slave_base_sequence::type_id::create("seq");

  for (int i = 0; i < number_of_bytes; i++) begin
    // req = i2c_item::type_id::create("req");
    // start_item(req);
    if ( !seq.randomize() with {
        transaction_type == local::transaction_type;
        data == local::data[i];
        ack_nack == local::ack_nack[i];
        clock_stretch_ack == local::clock_stretch_ack[i];
        foreach (local::clock_stretch_data[i][j]) {
          clock_stretch_data[j] == local::clock_stretch_data[i][j];
        }
      }
    ) `uvm_error("Slave Sequence", $sformatf("Multibyte Sequence Randomization failed at %0d", i))
    // finish_item(req);
    // get_response(rsp);
    seq.start(p_sequencer, this);
  end

endtask

class i2c_slave_read_sequence extends i2c_slave_base_sequence;
  `uvm_object_utils(i2c_slave_read_sequence)

  i2c_slave_base_sequence     seq;

  rand int                    number_of_bytes;
  rand bit                    ignore_register;

  // Item fields for slave Seq
  rand bit                    target_ack_nack;
  rand bit                    register_ack_nack;
  rand bit                    data_ack_nack[];
  rand int                    clock_stretch_ack[];
  rand int                    clock_stretch_data[][8];

  constraint c_slave_read_nob {
    number_of_bytes > 0;
    soft (number_of_bytes < 20); 
  }
  constraint c_slave_read_array_size {
    data_ack_nack.size() == number_of_bytes;
    clock_stretch_ack.size() == number_of_bytes;
    clock_stretch_data.size() == number_of_bytes;
  }
  constraint c_slave_read_ack_nack {
    soft (target_ack_nack == `ACK);
    soft (register_ack_nack == `ACK);
    foreach (data_ack_nack[i]) {
      soft (data_ack_nack[i] == `ACK);
    }
  }
  constraint c_slave_read_clock_stretch_ack_nack {
    foreach(clock_stretch_ack[i]) {
      clock_stretch_ack[i] >= 0;
      soft (clock_stretch_ack[i] == 0);
    }
  }
  constraint c_slave_read_clock_stretch_data  {
    foreach (clock_stretch_data[i]) {
      foreach (clock_stretch_data[i][j]) {
        clock_stretch_data[i][j] >= 0;
        soft (clock_stretch_data[i][j] == 0);
      }
    } 
  }
  constraint c_slave_read_ignore_reg {
    soft (ignore_register == 'b0);
  }

  // Introduce zero clock stretching on target and register addressing
  // constraint c_slave_read_normal_clock_stretch_behavior {
  //   clock_stretch_ack[0] == 0;
  //   clock_stretch_ack[1] == 0;
  //   foreach (clock_stretch_data[0][i]) {
  //     clock_stretch_data[0][i] == 0;
  //     clock_stretch_data[1][i] == 0;
  //   }
  // }
  
  extern function new(string name = "i2c_slave_read_sequence");
  extern virtual task body();

endclass // i2c_slave_read_sequence

function i2c_slave_read_sequence:: new(string name = "i2c_slave_read_sequence");
  super.new(name);
endfunction // i2c_slave_read_sequence::new

task i2c_slave_read_sequence:: body();
  int exit_flag;

  seq = i2c_slave_base_sequence::type_id::create("seq");

  while (1) begin
    exit_flag = 0;

    // Get target address
    if ( !seq.randomize() with { 
        transaction_type == READ;
        ack_nack == target_ack_nack;
      }
    ) `uvm_error("Master Sequence", "Write Sequence Randomization failed at Target Adress")
    seq.start(p_sequencer, this);
    exit_flag = seq.check_exit(stop_on_fail, stop_on_nack);
    if (exit_flag) continue;

    // Get register address
    if (!ignore_register) begin
      if ( !seq.randomize() with { 
          transaction_type == READ;
          ack_nack == register_ack_nack;
        }
      ) `uvm_error("Master Sequence", "Write Sequence Randomization failed at Register Address")
      seq.start(p_sequencer, this);
      exit_flag = seq.check_exit(stop_on_fail, stop_on_nack);
      if (exit_flag) continue;
    end

    // Read data
    for ( int i = 0; i < number_of_bytes; i++) begin
      if ( !seq.randomize() with { 
          transaction_type == READ;
          ack_nack == data_ack_nack[i];
          clock_stretch_ack == local::clock_stretch_ack[i];
          foreach (local::clock_stretch_data[i][j]) {
            clock_stretch_data[j] == local::clock_stretch_data[i][j];
          }
        }
      ) `uvm_error("Master Sequence", $sformatf("Write Sequence Randomization failed at %3d", i))
      seq.start(p_sequencer, this);
      exit_flag = seq.check_exit(stop_on_fail, stop_on_nack);
      if (exit_flag) break;
    end
    if (exit_flag) continue;

    // SEQUENCE FINISHED
    break;
  end

endtask 

class i2c_slave_write_sequence extends i2c_slave_base_sequence;
  `uvm_object_utils(i2c_slave_write_sequence)

  i2c_slave_base_sequence         seq;
  i2c_slave_multibyte_sequence    mb_seq;

  rand int                        number_of_bytes;
  rand bit                        ignore_register;

  // Item fields for slave Seq
  rand bit                        target_ack_nack;
  rand bit                        register_ack_nack;
  rand bit[7:0]                   data[];
  rand int                        clock_stretch_ack[];
  rand int                        clock_stretch_data[][8];

  constraint c_slave_write_nob {
    number_of_bytes > 0;
    soft (number_of_bytes < 20); 
  }
  constraint c_slave_write_array_size {
    data.size() == number_of_bytes;
    clock_stretch_ack.size() == number_of_bytes;
    clock_stretch_data.size() == number_of_bytes;
  }
  constraint c_slave_write_ack_nack {
    soft (target_ack_nack == `ACK);
    soft (register_ack_nack == `ACK);
  }
  constraint c_slave_write_clock_stretch_ack_nack {
    foreach(clock_stretch_ack[i]) {
      clock_stretch_ack[i] >= 0;
      soft (clock_stretch_ack[i] == 0);
    }
  }
  constraint c_slave_write_clock_stretch_data  {
    foreach (clock_stretch_data[i]) {
      foreach (clock_stretch_data[i][j]) {
        clock_stretch_data[i][j] >= 0;
        soft (clock_stretch_data[i][j] == 0);
      }
    } 
  }
  constraint c_slave_write_ignore_reg {
    soft (ignore_register == 'b0);
  }
  
  extern function new(string name = "i2c_slave_write_sequence");
  extern virtual task body();

endclass // i2c_slave_write_sequence

function i2c_slave_write_sequence:: new(string name = "i2c_slave_write_sequence");
  super.new(name);
endfunction

task i2c_slave_write_sequence:: body();
  int exit_flag;

  seq = i2c_slave_base_sequence::type_id::create("seq");

  while (1) begin
    exit_flag = 0;

    // Get target address
    if (!seq.randomize() with { 
        transaction_type == READ;
        ack_nack == target_ack_nack;
      }
    ) `uvm_error("RANDSEQ", "Read Sequence Randomization failed at Target Adress")
    seq.start(p_sequencer, this);
    exit_flag = seq.check_exit(stop_on_fail, stop_on_nack);
    if (exit_flag) continue;

    // Get register address
    if (!ignore_register) begin
      if (!seq.randomize() with { 
          transaction_type == READ;
          ack_nack == register_ack_nack;
        }
      ) `uvm_error("RANDSEQ", "Read Sequence Randomization failed at Register Address")
      seq.start(p_sequencer, this);
      exit_flag = seq.check_exit(stop_on_fail, stop_on_nack);
      if (exit_flag) continue;
    end

    // Get target address again (to write)
    if (!seq.randomize() with { 
        transaction_type == READ;
        ack_nack == target_ack_nack;
      }
    ) `uvm_error("RANDSEQ", "Read Sequence Randomization failed at Target Adress")
    seq.start(p_sequencer, this);
    exit_flag = seq.check_exit(stop_on_fail, stop_on_nack);
    if (exit_flag) continue;

    for ( int i = 0; i < number_of_bytes; i++) begin
      if ( !seq.randomize() with { 
          transaction_type == WRITE;
          data == data[i];
          if (local::i == number_of_bytes-1)  {ack_nack == `NACK;}
          clock_stretch_ack == local::clock_stretch_ack[i];
          foreach (local::clock_stretch_ack[i][j]) {
            clock_stretch_data[j] == local::clock_stretch_data[i][j];
          }
        }
      ) `uvm_error("Master Sequence", $sformatf("Read Sequence Randomization failed at %3d", i))
      seq.start(p_sequencer, this);
      exit_flag = seq.check_exit(stop_on_fail, stop_on_nack);
      if (exit_flag) break;
    end
    if (exit_flag == 1) continue;

    // SEQUENCE FINISHED
    break;
  end

endtask 