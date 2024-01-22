// *** Basic Sequences ***
class i2c_master_multibyte_sequence extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_multibyte_sequence)

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
  constraint c_master_mb_start_stop {
    soft (start_condition == 'b1);
    soft (stop_condition == 'b1);
  }
  constraint c_master_mb_array_size {
    data.size() == number_of_bytes;
    ack_nack.size() == number_of_bytes;
    delay.size() == number_of_bytes; 
  }
  constraint c_master_mb_ack_nack {
    foreach (ack_nack[i]) {
      soft (ack_nack[i] == `ACK);
    }
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
      int exit_flag = 0;

      if ( !seq.randomize() with { 
          transaction_type == local::transaction_type;
          data == local::data[i];
          ack_nack == local::ack_nack[i];
          if (local::i == 0)                  {start_condition == local::start_condition;}
          if (local::i == number_of_bytes-1)  {stop_condition == local::stop_condition;}
          delay == local::delay[i];
        }
      ) `uvm_error(get_type_name(), $sformatf("Multibyte Sequence Randomization failed at %0d", i))
      seq.start(p_sequencer, this);
      exit_flag = check_exit();
      if (exit_flag) begin
        if (stop_on_fail) return;
        if (stop_on_nack) return;
      end
    end
  endtask 

class i2c_master_write_sequence extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_write_sequence)

  i2c_master_base_sequence    seq;

  rand int                    number_of_bytes;
  rand bit                    ignore_register;

  // Item fields for Master Seq
  rand bit[7:1]               target_address;
  rand bit[7:0]               register_address;
  rand bit                    stop_condition;
  rand bit[7:0]               data[];
  rand int                    delay[];

  constraint c_master_write_target {
    soft ( !(target_address inside {RESERVED_ADDRESSES}) );
  }
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
    int exit_flag;

    seq = i2c_master_base_sequence::type_id::create("seq");

    while (1) begin
      exit_flag = 0;
      
      // Send target address
      if ( !seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b1;
          data == { target_address, `W };
          delay == local::delay[0];
        }
      ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag == 1) continue;
      if (exit_flag == 2) return;

      // Send register address
      if (!ignore_register) begin
        if ( !seq.randomize() with { 
            transaction_type == WRITE;
            data == register_address;
            delay == local::delay[1];
          }
        ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Register Address")
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), "Sent register address", UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      for ( int i = 0; i < number_of_bytes; i++) begin
        if ( !seq.randomize() with { 
            transaction_type == WRITE;
            data == local::data[i];
            if (local::i == number_of_bytes-1)  {
              stop_condition == local::stop_condition;
            }
            delay == local::delay[i+2];
          }
        ) `uvm_error(get_type_name(), $sformatf("Write Sequence Randomization failed at %3d", i))
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), $sformatf("Sent Data Byte %03d", i), UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // SEQUENCE FINISHED
      break; // or return;
    end

  endtask 

class i2c_master_read_sequence extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_read_sequence)

  i2c_master_base_sequence    seq;
  rand int                    number_of_bytes;
  rand bit                    ignore_register;

  // Item fields for Master Seq
  rand bit[7:1]               target_address;
  rand bit[7:0]               register_address;
  rand bit                    stop_condition;
  rand bit[7:0]               ack_nack[];
  rand int                    delay[];

  constraint c_master_read_target {
    soft ( !(target_address inside {RESERVED_ADDRESSES}) );
  }
  constraint c_master_read_nob {
    number_of_bytes > 0;
    soft (number_of_bytes < 20); 
  }
  constraint c_master_read_array_size {
    ack_nack.size() == number_of_bytes-1;
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
    int exit_flag;

    seq = i2c_master_base_sequence::type_id::create("seq");

    while (1) begin
      exit_flag = 0;

      // Send target address
      if ( !seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b1;
          data == { target_address, `W };
          delay == local::delay[0];
        }
      ) `uvm_error(get_type_name(), "Read Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag == 1) continue;
      if (exit_flag == 2) return;

      // Send register address
      if (!ignore_register) begin
        if ( !seq.randomize() with { 
            transaction_type == WRITE;
            data == register_address;
            delay == local::delay[1];
          }
        ) `uvm_error(get_type_name(), "Read Sequence Randomization failed at Register Address")
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), "Sent register address", UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // Send target address again (read)
      if ( !seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b1;
          data == { target_address, `R };
          delay == local::delay[2];
        }
      )  `uvm_error(get_type_name(), "Read Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent target address (R)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag) return;
      

      for ( int i = 0; i < number_of_bytes; i++) begin
        if ( !seq.randomize() with { 
            transaction_type == READ;
            if (local::i == number_of_bytes-1)  {
              ack_nack == `NACK;
              stop_condition == local::stop_condition;
            }
            delay == local::delay[i+3];
          }
        ) `uvm_error(get_type_name(), $sformatf("Read Sequence Randomization failed at %3d", i))
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), $sformatf("Read Data Byte %03d", i), UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // SEQUENCE FINISHED
      break; // or return;
    end
  endtask 

// *** PreConfiged Sequences ***

// ** Write **
class i2c_master_write_with_stop_no_delays extends i2c_master_write_sequence;
  `uvm_object_utils(i2c_master_write_with_stop_no_delays)

  constraint c_master_write_with_stop_no_delays {
    stop_condition == 'b1;
    foreach (delay[i]) delay[i] == 0;
  }

  function new(string name = "i2c_master_write_with_stop_no_delays");
    super.new(name);
  endfunction
endclass

class i2c_master_write_with_stop_with_delays extends i2c_master_write_sequence;
  `uvm_object_utils(i2c_master_write_with_stop_with_delays)

  constraint c_master_write_with_stop_no_delays {
    stop_condition == 'b1;
    foreach (delay[i]) delay[i] inside {[1:30]};
  }

  function new(string name = "i2c_master_write_with_stop_with_delays");
    super.new(name);
  endfunction
endclass

class i2c_master_write_no_stop_no_delays extends i2c_master_write_sequence;
  `uvm_object_utils(i2c_master_write_no_stop_no_delays)

  constraint c_master_write_with_stop_no_delays {
    stop_condition == 'b0;
    foreach (delay[i]) delay[i] == 0;
  }

  function new(string name = "i2c_master_write_no_stop_no_delays");
    super.new(name);
  endfunction
endclass

class i2c_master_write_no_stop_with_delays extends i2c_master_write_sequence;
  `uvm_object_utils(i2c_master_write_no_stop_with_delays)

  constraint c_master_write_no_stop_with_delays{
    stop_condition == 'b0;
    foreach (delay[i]) delay[i] inside {[1:30]};
  }

  function new(string name = "i2c_master_write_no_stop_with_delays");
    super.new(name);
  endfunction
endclass


// ** Read **
class i2c_master_read_with_stop_no_delays extends i2c_master_read_sequence;
  `uvm_object_utils(i2c_master_read_with_stop_no_delays)

  constraint c_master_read_with_stop_no_delays {
    stop_condition == 'b1;
    foreach (delay[i]) delay[i] == 0;
  }

  function new(string name = "i2c_master_read_with_stop_no_delays");
    super.new(name);
  endfunction
endclass

class i2c_master_read_with_stop_with_delays extends i2c_master_read_sequence;
  `uvm_object_utils(i2c_master_read_with_stop_with_delays)

  constraint c_master_read_with_stop_with_delays {
    stop_condition == 'b1;
    foreach (delay[i]) delay[i] inside {[1:30]};
  }

  function new(string name = "i2c_master_read_with_stop_with_delays");
    super.new(name);
  endfunction
endclass

class i2c_master_read_no_stop_no_delays extends i2c_master_read_sequence;
  `uvm_object_utils(i2c_master_read_no_stop_no_delays)

  constraint c_master_read_no_stop_no_delays {
    stop_condition == 'b0;
    foreach (delay[i]) delay[i] == 0;
  }

  function new(string name = "i2c_master_read_no_stop_no_delays");
    super.new(name);
  endfunction
endclass

class i2c_master_read_no_stop_with_delays extends i2c_master_read_sequence;
  `uvm_object_utils(i2c_master_read_no_stop_with_delays)

  constraint c_master_read_no_stop_with_delays {
    stop_condition == 'b0;
    foreach (delay[i]) delay[i] inside {[1:30]};
  }

  function new(string name = "i2c_master_read_no_stop_with_delays");
    super.new(name);
  endfunction
endclass

// *** Reserved Adresses ***

class i2c_master_general_call_command extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_general_call_command)

  i2c_master_base_sequence    seq;

  rand bit[7:1]               command;
  rand int                    delay[2];

  constraint c_master_general_call_command {
    soft (command == 7'b000_0011);  // reset command
    foreach (delay[i]) soft (delay[i] == 0);
  }

  extern function new(string name = "i2c_master_general_call_command");
  extern virtual task body();
endclass

  function i2c_master_general_call_command:: new(string name = "i2c_master_general_call_command");
    super.new(name);
  endfunction

  task i2c_master_general_call_command:: body();
    seq = i2c_master_base_sequence::type_id::create("seq");

    while (1) begin
      if(!seq.randomize() with {
        start_condition == 'b1;
        data == 8'h00;
        delay == local::delay[0];
      }) `uvm_error("RANDERR", "General Call Address Randomization failed")
      seq.start(p_sequencer, this);
      if (seq.check_exit()) continue;

      if(!seq.randomize() with {
        data == {command, 1'b0};
        delay == local::delay[0];
        stop_condition == local::stop_condition;
      }) `uvm_error("RANDERR", "General Call Command Randomization failed")
      seq.start(p_sequencer, this);
      if (seq.check_exit()) continue;

      break;
    end
  endtask

class i2c_master_general_call_controller_address extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_general_call_controller_address)

  i2c_master_base_sequence    seq;

  rand bit[7:1]               controller_address;
  rand int                    delay[2];

  constraint c_master_general_call_controller_address {
    soft (controller_address == 7'b101_0011);  // default controller_address
    foreach (delay[i]) soft (delay[i] == 0);
  }

  extern function new(string name = "i2c_master_general_call_controller_address");
  extern virtual task body();
endclass

  function i2c_master_general_call_controller_address:: new(string name = "i2c_master_general_call_controller_address");
    super.new(name);
  endfunction

  task i2c_master_general_call_controller_address:: body();
    seq = i2c_master_base_sequence::type_id::create("seq");

    while (1) begin
      if(!seq.randomize() with {
        start_condition == 'b1;
        data == 8'h00;
        delay == local::delay[0];
      }) `uvm_error("RANDERR", "General Call Address Randomization failed")
      seq.start(p_sequencer, this);
      if (seq.check_exit()) continue;

      if(!seq.randomize() with {
        data == {controller_address, 1'b1};
        delay == local::delay[0];
        stop_condition == local::stop_condition;
      }) `uvm_error("RANDERR", "Controller Address Randomization failed")
      seq.start(p_sequencer, this);
      if (seq.check_exit()) continue;

      break;
    end
  endtask

class i2c_master_start_byte extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_start_byte)

  constraint c_master_start_byte {
    start_condition == 'b1;
    data == 8'b0000_0001;
  }

  function new(string name = "i2c_master_start_byte");
    super.new(name);
  endfunction

  virtual task body();
    while (1) begin
      super.body();
      if (!check_exit()) break;
    end
  endtask
endclass

class i2c_master_high_speed_mode extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_high_speed_mode)

  constraint c_master_high_speed_mode {
    start_condition == 'b1;
    data[7:3] == 5'b000_01;
  }

  function new(string name = "i2c_master_high_speed_mode");
    super.new(name);
  endfunction

  virtual task body();
    while (1) begin
      super.body();
      if (rsp.ack_nack == `ACK) `uvm_error("WRNGACK", "Did not expect ACK at Speed Mode Code")
      if (!check_exit()) break;
    end
  endtask
endclass

class i2c_master_device_id extends i2c_master_base_sequence;
  `uvm_object_utils(i2c_master_device_id)

  i2c_master_read_sequence    seq;

  bit[7:1]                    target_address;
  bit[7:1]                    device_id_address;

  constraint c_master_device_id {
    device_id_address inside {[7'b111_1100:7'b111_1111]};
  }

  function new(string name = "i2c_master_device_id");
    super.new(name);
  endfunction

  virtual task body();
    seq = i2c_master_read_sequence::type_id::create("seq");

    if (!seq.randomize() with {
      stop_condition == 0;
      target_address == device_id_address;
      ignore_register == 'b0;
      register_address == local::target_address;
      number_of_bytes == 3;
    }) `uvm_error("RANDERR", "Read Sequence randomization failed")
    seq.start(p_sequencer, this);
  endtask
endclass

class i2c_master_10bit_addr_write extends i2c_master_write_sequence;
  `uvm_object_utils(i2c_master_10bit_addr_write)

  rand bit[9:0]                 target_address_10bit;
  rand int                      init_delay;

  constraint c_master_10bit_addr_write {
    soft (init_delay inside {[1:30]});
  }

  function new(string name = "i2c_master_10bit_addr_write");
    super.new(name);
  endfunction

  virtual task body();
    int exit_flag = 0;
    seq = i2c_master_base_sequence::type_id::create("seq");

    while (1) begin
      exit_flag = 0;
      
      // Send target address (first 2 bits)
      if (!seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b1;
          data == { TEN_BIT_TARGET_ADDRESSING, target_address_10bit[9:8], `W };
          delay == local::init_delay;
        }
      ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent init 2 bits of 10 bit target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag == 1) continue;
      if (exit_flag == 2) return;

      // Send target address (remaining 8 bits)
      if ( !seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b0;
          data == target_address_10bit[7:0];
          delay == local::delay[0];
        }
      ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag == 1) continue;
      if (exit_flag == 2) return;

      // Send register address
      if (!ignore_register) begin
        if ( !seq.randomize() with { 
            transaction_type == WRITE;
            data == register_address;
            delay == local::delay[1];
          }
        ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Register Address")
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), "Sent register address", UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      for ( int i = 0; i < number_of_bytes; i++) begin
        if ( !seq.randomize() with { 
            transaction_type == WRITE;
            data == local::data[i];
            if (local::i == number_of_bytes-1)  {
              stop_condition == local::stop_condition;
            }
            delay == local::delay[i+2];
          }
        ) `uvm_error(get_type_name(), $sformatf("Write Sequence Randomization failed at %3d", i))
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), $sformatf("Sent Data Byte %03d", i), UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // SEQUENCE FINISHED
      break; // or return;
    end
  endtask
endclass

class i2c_master_10bit_addr_read extends i2c_master_read_sequence;
  `uvm_object_utils(i2c_master_10bit_addr_read)

  rand bit[9:0]                 target_address_10bit;
  rand int                      init_delay;

  constraint c_master_10bit_addr_read {
    soft (init_delay inside {[1:30]});
  }

  function new(string name = "i2c_master_10bit_addr_read");
    super.new(name);
  endfunction

  virtual task body();
    int exit_flag = 0;
    seq = i2c_master_base_sequence::type_id::create("seq");

    while (1) begin
      exit_flag = 0;

      // Send target address (first 2 bits)
      if (!seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b1;
          data == { TEN_BIT_TARGET_ADDRESSING, target_address_10bit[9:8], `W };
          delay == local::init_delay;
        }
      ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent init 2 bits of 10 bit target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag == 1) continue;
      if (exit_flag == 2) return;

      // Send target address (remaining 8 bits)
      if ( !seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b0;
          data == target_address_10bit[7:0];
          delay == local::delay[0];
        }
      ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag == 1) continue;
      if (exit_flag == 2) return;
      // Send register address
      if (!ignore_register) begin
        if ( !seq.randomize() with { 
            transaction_type == WRITE;
            data == register_address;
            delay == local::delay[1];
          }
        ) `uvm_error(get_type_name(), "Read Sequence Randomization failed at Register Address")
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), "Sent register address", UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // Send target address again (read)
      if ( !seq.randomize() with { 
          transaction_type == WRITE;
          start_condition == 'b1;
          data == { TEN_BIT_TARGET_ADDRESSING, target_address_10bit[9:8], `R };
          delay == local::delay[2];
        }
      )  `uvm_error(get_type_name(), "Read Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Sent target address (R)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag) return;
      

      for ( int i = 0; i < number_of_bytes; i++) begin
        if ( !seq.randomize() with { 
            transaction_type == READ;
            if (local::i == number_of_bytes-1)  {
              ack_nack == `NACK;
              stop_condition == local::stop_condition;
            }
            delay == local::delay[i+3];
          }
        ) `uvm_error(get_type_name(), $sformatf("Read Sequence Randomization failed at %3d", i))
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), $sformatf("Read Data Byte %03d", i), UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // SEQUENCE FINISHED
      break; // or return;
    end
  endtask
endclass