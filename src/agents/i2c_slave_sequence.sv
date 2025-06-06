// *** Basic Sequences ***
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
  constraint c_slave_mb_ack_nack {
    foreach (ack_nack[i]) {
      soft (ack_nack[i] == `ACK);
    }
  }
  constraint c_slave_mb_clock_stretch_ack  {
    foreach (clock_stretch_ack[i]) {
        clock_stretch_ack[i] >= 0;
        soft (clock_stretch_ack[i] == 0);
    } 
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
      int exit_flag = 0;
      if ( !seq.randomize() with {
          transaction_type == local::transaction_type;
          data == local::data[i];
          ack_nack == local::ack_nack[i];
          clock_stretch_ack == local::clock_stretch_ack[i];
          foreach (local::clock_stretch_data[i][j]) {
            clock_stretch_data[j] == local::clock_stretch_data[i][j];
          }
        }
      ) `uvm_error(get_type_name(), $sformatf("Multibyte Sequence Randomization failed at %0d", i))
      seq.start(p_sequencer, this);
      exit_flag = seq.check_exit();
      if (exit_flag) begin
        if (stop_on_fail) return;
        if (stop_on_nack) return;
      end
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
  
  extern function new(string name = "i2c_slave_read_sequence");
  extern virtual task body();
endclass // i2c_slave_read_sequence

  function i2c_slave_read_sequence:: new(string name = "i2c_slave_read_sequence");
    super.new(name);
  endfunction // i2c_slave_read_sequence::new

  task i2c_slave_read_sequence:: body();
    int exit_flag;

    seq = i2c_slave_base_sequence::type_id::create("seq");

    forever begin
      exit_flag = 0;

      // Get target address
      if ( !seq.randomize() with { 
          transaction_type == READ;
          ack_nack == target_ack_nack;
        }
      ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Read target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag) return;

      // Get register address
      if (!ignore_register) begin
        if ( !seq.randomize() with { 
            transaction_type == READ;
            ack_nack == register_ack_nack;
          }
        ) `uvm_error(get_type_name(), "Write Sequence Randomization failed at Register Address")
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), "Read register address", UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
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
        ) `uvm_error(get_type_name(), $sformatf("Write Sequence Randomization failed at %3d", i))
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), $sformatf("Read Data Byte %03d", i), UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // SEQUENCE FINISHED
      break; // or return;
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

    forever begin
      exit_flag = 0;

      // Get target address
      if ( !seq.randomize() with { 
          transaction_type == READ;
          ack_nack == target_ack_nack;
        } 
      ) `uvm_error(get_type_name(), "Read Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Read target address (W)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag) return;
      
      // Get register address
      if (!ignore_register) begin
        if ( !seq.randomize() with { 
            transaction_type == READ;
            ack_nack == register_ack_nack;
          } 
        ) `uvm_error(get_type_name(), "Read Sequence Randomization failed at Register Address")
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), "Read register address", UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // Get target address again (to write)
      if ( !seq.randomize() with { 
          transaction_type == READ;
          ack_nack == target_ack_nack;
        }
      ) `uvm_error(get_type_name(), "Read Sequence Randomization failed at Target Adress")
      seq.start(p_sequencer, this);
      `uvm_info(get_name(), "Read target address (R)", UVM_MEDIUM)
      exit_flag = seq.check_exit();
      if (exit_flag) return;

      for ( int i = 0; i < number_of_bytes; i++) begin
        if ( !seq.randomize() with { 
            transaction_type == WRITE;
            data == local::data[i];
            if (local::i == number_of_bytes-1)  {ack_nack == `NACK;}
            clock_stretch_ack == local::clock_stretch_ack[i];
            foreach (local::clock_stretch_data[i][j]) {
              clock_stretch_data[j] == local::clock_stretch_data[i][j];
            }
          }
        ) `uvm_error(get_type_name(), $sformatf("Read Sequence Randomization failed at %3d", i))
        seq.start(p_sequencer, this);
        `uvm_info(get_name(), $sformatf("Sent Data Byte %03d", i), UVM_MEDIUM)
        exit_flag = seq.check_exit();
        if (exit_flag) return;
      end

      // SEQUENCE FINISHED
      break; // or return;
    end
  endtask

// *** PreConfiged Sequences ***

class i2c_slave_read_with_clock_stretch_ack extends i2c_slave_read_sequence;
  `uvm_object_utils(i2c_slave_read_with_clock_stretch_ack)

  constraint c_slave_read_with_clock_stretch_ack {
    foreach (clock_stretch_ack[i]) soft (clock_stretch_ack[i] inside {[10:40]});
  }

  function new(string name = "i2c_slave_read_with_clock_stretch_ack");
    super.new(name);
  endfunction
endclass

class i2c_slave_read_with_clock_stretch_all extends i2c_slave_read_sequence;
  `uvm_object_utils(i2c_slave_read_with_clock_stretch_all)

  constraint c_slave_read_with_clock_stretch_ack {
    foreach (clock_stretch_ack[i]) soft (clock_stretch_ack[i] inside {[10:50]});
    foreach (clock_stretch_data[i,j]) soft (clock_stretch_data[i][j] inside {[10:30]});
  }

  function new(string name = "i2c_slave_read_with_clock_stretch_all");
    super.new(name);
  endfunction
endclass

class i2c_slave_write_with_clock_stretch_ack extends i2c_slave_write_sequence;
  `uvm_object_utils(i2c_slave_write_with_clock_stretch_ack)

  constraint c_slave_write_with_clock_stretch_ack {
    foreach (clock_stretch_ack[i]) soft (clock_stretch_ack[i] inside {[10:40]});
  }

  function new(string name = "i2c_slave_write_with_clock_stretch_ack");
    super.new(name);
  endfunction
endclass

class i2c_slave_write_with_clock_stretch_all extends i2c_slave_write_sequence;
  `uvm_object_utils(i2c_slave_write_with_clock_stretch_all)

  constraint c_slave_write_with_clock_stretch_ack {
    foreach (clock_stretch_ack[i]) soft (clock_stretch_ack[i] inside {[10:50]});
    foreach (clock_stretch_data[i,j]) soft (clock_stretch_data[i][j] inside {[10:30]});
  }

  function new(string name = "i2c_slave_write_with_clock_stretch_all");
    super.new(name);
  endfunction
endclass