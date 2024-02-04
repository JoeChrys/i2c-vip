class i2c_virtual_multibyte_sequence extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_multibyte_sequence)

  i2c_master_multibyte_sequence  m_seq;
  i2c_slave_multibyte_sequence   s_seq;

  rand bit[7:0]         data[];
  rand bit              ack_nack[];
  rand int              delay[];
  rand int              clock_stretch_data[][8];
  rand int              clock_stretch_ack[];

  constraint c_virtual_mb_nob {
    number_of_bytes > 0;
    soft (number_of_bytes < 8);
  }
  constraint c_virtual_mb_start_stop {
    soft (start_condition == 1);
    soft (stop_condition == 1);
  }
  constraint c_virtual_mb_array_size {
    data.size() == number_of_bytes;
    ack_nack.size() == number_of_bytes;
    delay.size() == number_of_bytes;
    clock_stretch_ack.size() == number_of_bytes;
    clock_stretch_data.size() == number_of_bytes;
  }
  constraint c_virtual_mb_defaults {
    foreach (delay[i]) {
      delay[i] >= 0; 
      soft (delay[i] == 0);
    }
    foreach (clock_stretch_ack[i]) {
      clock_stretch_ack[i] >= 0;
      soft (clock_stretch_ack[i] == 0);
    }
    foreach (clock_stretch_data[i,j]) {
      clock_stretch_data[i][j] >= 0;
      soft (clock_stretch_data[i][j] == 0);
    }
  }
  constraint c_virtual_mb_ack_nack {
    foreach (ack_nack[i]) {
      soft (ack_nack[i] == `ACK);
    }
  }

  extern function new(string name = "i2c_virtual_multibyte_sequence");
  extern virtual task body();
endclass

  function i2c_virtual_multibyte_sequence:: new(string name = "i2c_virtual_multibyte_sequence");
    super.new(name);
  endfunction

  task i2c_virtual_multibyte_sequence:: body();
    m_seq = i2c_master_multibyte_sequence::type_id::create("m_seq");
    s_seq = i2c_slave_multibyte_sequence::type_id::create("s_seq");

    fork
      begin
        if (!m_seq.randomize() with {
          transaction_type == local::transaction_type;
          data == local::data;
          ack_nack == local::ack_nack;
          start_condition == local::start_condition;
          stop_condition == local::stop_condition;
          delay == local::delay;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          if (transaction_type == WRITE) transaction_type == READ;
          else if (transaction_type == READ) transaction_type == WRITE;
          data == local::data;
          ack_nack == local::ack_nack;
          foreach (clock_stretch_ack[i]) {clock_stretch_ack[i] == local::clock_stretch_ack[i]};
          foreach (clock_stretch_data[i,j]) {
            clock_stretch_data[i][j] == local::clock_stretch_data[i][j];
          }
        })
        `uvm_fatal("RNDERR", "Failed to randomize slave sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

// *** No delays / Clock Stretch

class i2c_virtual_write_with_stop_no_delays_no_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_write_with_stop_no_delays_no_cs)

  i2c_master_write_with_stop_no_delays  m_seq;
  i2c_slave_read_sequence             s_seq;

  extern function new(string name = "i2c_virtual_write_with_stop_no_delays_no_cs");
  extern virtual task body();
endclass

  function i2c_virtual_write_with_stop_no_delays_no_cs:: new(string name = "i2c_virtual_write_with_stop_no_delays_no_cs");
    super.new(name);
  endfunction

  task i2c_virtual_write_with_stop_no_delays_no_cs:: body();
    m_seq = i2c_master_write_with_stop_no_delays::type_id::create("m_seq");
    s_seq = i2c_slave_read_sequence::type_id::create("s_seq");
    
    // if (!uvm_config_db#(i2c_master_sequencer)::get(null,"uvm_test_top.v_seq*","m_seqr", m_seqr) ) 
    //   `uvm_fatal("NULPTR", "Master Sequencer has not be set")
    // if (!uvm_config_db#(i2c_slave_sequencer)::get(null,"uvm_test_top.v_seq*","p_sequencer.s_seqr", p_sequencer.s_seqr) ) 
    //  `uvm_fatal("NULPTR", "Slave Sequencer has not be set")

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_write_no_stop_no_delays_no_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_write_no_stop_no_delays_no_cs)

  i2c_master_write_no_stop_no_delays  m_seq;
  i2c_slave_read_sequence             s_seq;

  extern function new(string name = "i2c_virtual_write_no_stop_no_delays_no_cs");
  extern virtual task body();
endclass

  function i2c_virtual_write_no_stop_no_delays_no_cs:: new(string name = "i2c_virtual_write_no_stop_no_delays_no_cs");
    super.new(name);
  endfunction

  task i2c_virtual_write_no_stop_no_delays_no_cs:: body();
    m_seq = i2c_master_write_no_stop_no_delays::type_id::create("m_seq");
    s_seq = i2c_slave_read_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_read_with_stop_no_delays_no_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_read_with_stop_no_delays_no_cs)

  i2c_master_read_with_stop_no_delays  m_seq;
  i2c_slave_write_sequence             s_seq;

  extern function new(string name = "i2c_virtual_read_with_stop_no_delays_no_cs");
  extern virtual task body();
endclass

  function i2c_virtual_read_with_stop_no_delays_no_cs:: new(string name = "i2c_virtual_read_with_stop_no_delays_no_cs");
    super.new(name);
  endfunction

  task i2c_virtual_read_with_stop_no_delays_no_cs:: body();
    m_seq = i2c_master_read_with_stop_no_delays::type_id::create("m_seq");
    s_seq = i2c_slave_write_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_read_no_stop_no_delays_no_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_read_no_stop_no_delays_no_cs)

  i2c_master_read_no_stop_no_delays  m_seq;
  i2c_slave_write_sequence           s_seq;

  extern function new(string name = "i2c_virtual_read_no_stop_no_delays_no_cs");
  extern virtual task body();
endclass

  function i2c_virtual_read_no_stop_no_delays_no_cs:: new(string name = "i2c_virtual_read_no_stop_no_delays_no_cs");
    super.new(name);
  endfunction

  task i2c_virtual_read_no_stop_no_delays_no_cs:: body();
    m_seq = i2c_master_read_no_stop_no_delays::type_id::create("m_seq");
    s_seq = i2c_slave_write_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

// *** With delay and Clock Stretch

// * Write
class i2c_virtual_write_with_stop_with_delays_with_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_write_with_stop_with_delays_with_cs)

  i2c_master_write_with_stop_with_delays  m_seq;
  i2c_slave_read_with_clock_stretch_ack   s_seq;

  extern function new(string name = "i2c_virtual_write_with_stop_with_delays_with_cs");
  extern virtual task body();
endclass

  function i2c_virtual_write_with_stop_with_delays_with_cs:: new(string name = "i2c_virtual_write_with_stop_with_delays_with_cs");
    super.new(name);
  endfunction

  task i2c_virtual_write_with_stop_with_delays_with_cs:: body();
    m_seq = i2c_master_write_with_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_read_with_clock_stretch_ack::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_write_no_stop_with_delays_with_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_write_no_stop_with_delays_with_cs)

  i2c_master_write_no_stop_with_delays  m_seq;
  i2c_slave_read_with_clock_stretch_ack   s_seq;

  extern function new(string name = "i2c_virtual_write_no_stop_with_delays_with_cs");
  extern virtual task body();
endclass

  function i2c_virtual_write_no_stop_with_delays_with_cs:: new(string name = "i2c_virtual_write_no_stop_with_delays_with_cs");
    super.new(name);
  endfunction

  task i2c_virtual_write_no_stop_with_delays_with_cs:: body();
    m_seq = i2c_master_write_no_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_read_with_clock_stretch_ack::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_write_with_stop_with_delays_with_cs_all extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_write_with_stop_with_delays_with_cs_all)

  i2c_master_write_with_stop_with_delays  m_seq;
  i2c_slave_read_with_clock_stretch_all   s_seq;

  extern function new(string name = "i2c_virtual_write_with_stop_with_delays_with_cs_all");
  extern virtual task body();
endclass

  function i2c_virtual_write_with_stop_with_delays_with_cs_all:: new(string name = "i2c_virtual_write_with_stop_with_delays_with_cs_all");
    super.new(name);
  endfunction

  task i2c_virtual_write_with_stop_with_delays_with_cs_all:: body();
    m_seq = i2c_master_write_with_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_read_with_clock_stretch_all::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_write_no_stop_with_delays_with_cs_all extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_write_no_stop_with_delays_with_cs_all)

  i2c_master_write_no_stop_with_delays  m_seq;
  i2c_slave_read_with_clock_stretch_all   s_seq;

  extern function new(string name = "i2c_virtual_write_no_stop_with_delays_with_cs_all");
  extern virtual task body();
endclass

  function i2c_virtual_write_no_stop_with_delays_with_cs_all:: new(string name = "i2c_virtual_write_no_stop_with_delays_with_cs_all");
    super.new(name);
  endfunction

  task i2c_virtual_write_no_stop_with_delays_with_cs_all:: body();
    m_seq = i2c_master_write_no_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_read_with_clock_stretch_all::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

// * Read
class i2c_virtual_read_with_stop_with_delays_with_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_read_with_stop_with_delays_with_cs)

  i2c_master_read_with_stop_with_delays     m_seq;
  i2c_slave_write_with_clock_stretch_ack    s_seq;

  extern function new(string name = "i2c_virtual_read_with_stop_with_delays_with_cs");
  extern virtual task body();
endclass

  function i2c_virtual_read_with_stop_with_delays_with_cs:: new(string name = "i2c_virtual_read_with_stop_with_delays_with_cs");
    super.new(name);
  endfunction

  task i2c_virtual_read_with_stop_with_delays_with_cs:: body();
    m_seq = i2c_master_read_with_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_write_with_clock_stretch_ack::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_read_no_stop_with_delays_with_cs extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_read_no_stop_with_delays_with_cs)

  i2c_master_read_no_stop_with_delays       m_seq;
  i2c_slave_write_with_clock_stretch_ack    s_seq;

  extern function new(string name = "i2c_virtual_read_no_stop_with_delays_with_cs");
  extern virtual task body();
endclass

  function i2c_virtual_read_no_stop_with_delays_with_cs:: new(string name = "i2c_virtual_read_no_stop_with_delays_with_cs");
    super.new(name);
  endfunction

  task i2c_virtual_read_no_stop_with_delays_with_cs:: body();
    m_seq = i2c_master_read_no_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_write_with_clock_stretch_ack::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_read_with_stop_with_delays_with_cs_all extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_read_with_stop_with_delays_with_cs_all)

  i2c_master_read_with_stop_with_delays     m_seq;
  i2c_slave_write_with_clock_stretch_all    s_seq;

  extern function new(string name = "i2c_virtual_read_with_stop_with_delays_with_cs_all");
  extern virtual task body();
endclass

  function i2c_virtual_read_with_stop_with_delays_with_cs_all:: new(string name = "i2c_virtual_read_with_stop_with_delays_with_cs_all");
    super.new(name);
  endfunction

  task i2c_virtual_read_with_stop_with_delays_with_cs_all:: body();
    m_seq = i2c_master_read_with_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_write_with_clock_stretch_all::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_read_no_stop_with_delays_with_cs_all extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_read_no_stop_with_delays_with_cs_all)

  i2c_master_read_no_stop_with_delays       m_seq;
  i2c_slave_write_with_clock_stretch_all    s_seq;

  extern function new(string name = "i2c_virtual_read_no_stop_with_delays_with_cs_all");
  extern virtual task body();
endclass

  function i2c_virtual_read_no_stop_with_delays_with_cs_all:: new(string name = "i2c_virtual_read_no_stop_with_delays_with_cs_all");
    super.new(name);
  endfunction

  task i2c_virtual_read_no_stop_with_delays_with_cs_all:: body();
    m_seq = i2c_master_read_no_stop_with_delays::type_id::create("m_seq");
    s_seq = i2c_slave_write_with_clock_stretch_all::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

// * Reserved Addresses

class i2c_virtual_general_call_command extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_general_call_command)

  i2c_master_general_call_command  m_seq;

  rand bit[7:1]               command;
  rand int                    delay[2];
  rand int                    clock_stretch_ack[2];
  rand int                    clock_stretch_data[2][8];

  constraint c_virtual_general_call_command_defaults {
    soft (command == 7'b000_0011);  // reset command
    foreach(delay[i]) {
      delay[i] >= 0;
      soft (delay[i] == 0);
    }
    foreach(clock_stretch_ack[i]) {
      clock_stretch_ack[i] >= 0;
      soft (clock_stretch_ack[i] == 0);
    }
    foreach (clock_stretch_data[i]) {
      foreach (clock_stretch_data[i][j]) {
        clock_stretch_data[i][j] >= 0;
        soft (clock_stretch_data[i][j] == 0);
      }
    } 
  }

  extern function new(string name = "i2c_virtual_general_call_command");
  extern virtual task body();
endclass

  function i2c_virtual_general_call_command:: new(string name = "i2c_virtual_general_call_command");
    super.new(name);
  endfunction

  task i2c_virtual_general_call_command:: body();
    m_seq = i2c_master_general_call_command::type_id::create("m_seq");
    s_seq = i2c_slave_base_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          command == local::command;
          delay[0] == local::delay[0];
          delay[1] == local::delay[1];
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        foreach (clock_stretch_ack[i]) begin
          if (!s_seq.randomize() with {
            clock_stretch_ack[i] == local::clock_stretch_ack[i];
            foreach (clock_stretch_data[i][j]) {
              clock_stretch_data[i][j] == local::clock_stretch_data[i][j];
            }
          })
          `uvm_fatal("RNDERR", "Failed to randomize slave sequence")
          s_seq.start(p_sequencer.s_seqr, this);
        end
      end
    join
  endtask

class i2c_virtual_general_call_controller_address extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_general_call_controller_address)

  i2c_master_general_call_controller_address  m_seq;

  rand bit[7:1]               controller_address;
  rand int                    delay[2];
  rand int                    clock_stretch_ack[2];
  rand int                    clock_stretch_data[2][8];

  constraint i2c_virtual_general_call_controller_address_defaults {
    soft (controller_address == 7'b101_0011);  // default controller_address
    foreach(delay[i]) {
      delay[i] >= 0;
      soft (delay[i] == 0);
    }
    foreach(clock_stretch_ack[i]) {
      clock_stretch_ack[i] >= 0;
      soft (clock_stretch_ack[i] == 0);
    }
    foreach (clock_stretch_data[i]) {
      foreach (clock_stretch_data[i][j]) {
        clock_stretch_data[i][j] >= 0;
        soft (clock_stretch_data[i][j] == 0);
      }
    } 
  }

  extern function new(string name = "i2c_virtual_general_call_controller_address");
  extern virtual task body();
endclass

  function i2c_virtual_general_call_controller_address:: new(string name = "i2c_virtual_general_call_controller_address");
    super.new(name);
  endfunction

  task i2c_virtual_general_call_controller_address:: body();
    m_seq = i2c_master_general_call_controller_address::type_id::create("m_seq");
    s_seq = i2c_slave_base_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          controller_address == local::controller_address;
          delay[0] == local::delay[0];
          delay[1] == local::delay[1];
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        foreach (clock_stretch_ack[i]) begin
          if (!s_seq.randomize() with {
            clock_stretch_ack[i] == local::clock_stretch_ack[i];
            foreach (clock_stretch_data[i][j]) {
              clock_stretch_data[i][j] == local::clock_stretch_data[i][j];
            }
          })
          `uvm_fatal("RNDERR", "Failed to randomize slave sequence")
          s_seq.start(p_sequencer.s_seqr, this);
        end
      end
    join
  endtask

class i2c_virtual_device_id extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_device_id)

  i2c_master_device_id      m_seq;
  i2c_slave_write_sequence   s_seq;

  rand bit[11:0] manufacturer_id;
  rand bit[8:0]  part_number;
  rand bit[2:0]  revision;

  extern function new(string name = "i2c_virtual_device_id");
  extern virtual task body();
endclass

  function i2c_virtual_device_id:: new(string name = "i2c_virtual_device_id");
    super.new(name);
  endfunction

  task i2c_virtual_device_id:: body();
    m_seq = i2c_master_device_id::type_id::create("m_seq");
    s_seq = i2c_slave_write_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          stop_condition == local::stop_condition;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == 3;
          data[0] == local::manufacturer_id[11:4];
          data[1] == {local::manufacturer_id[3:0],local::part_number[8:5]};
          data[2] == {local::part_number[4:0],local::revision};
        })
        `uvm_fatal("RNDERR", "Failed to randomize slave sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_cbus extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_cbus)

  i2c_master_write_sequence  m_seq;
  i2c_slave_read_sequence   s_seq;

  rand bit[7:0] data[];
  rand bit ack_nack[];
  rand bit     stop_condition;

  extern function new(string name = "i2c_virtual_cbus");
  extern virtual task body();
endclass

  function i2c_virtual_cbus:: new(string name = "i2c_virtual_cbus");
    super.new(name);
  endfunction

  task i2c_virtual_cbus:: body();
    m_seq = i2c_master_write_sequence::type_id::create("m_seq");
    s_seq = i2c_slave_read_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          target_address == C_BUS;
          number_of_bytes == local::number_of_bytes;
          stop_condition == local::stop_condition;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
          foreach (local::ack_nack[i]) {
            data_ack_nack[i] dist {`ACK:=1, `NACK:=1};
          }
        })
        `uvm_fatal("RNDERR", "Failed to randomize slave sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask

class i2c_virtual_other_bus extends i2c_virtual_base_sequence;
  `uvm_object_utils(i2c_virtual_other_bus)

  i2c_master_write_sequence  m_seq;
  i2c_slave_read_sequence   s_seq;

  rand bit[7:0] data[];
  rand bit ack_nack[];
  rand bit     stop_condition;

  extern function new(string name = "i2c_virtual_other_bus");
  extern virtual task body();
endclass

  function i2c_virtual_other_bus:: new(string name = "i2c_virtual_other_bus");
    super.new(name);
  endfunction

  task i2c_virtual_other_bus:: body();
    m_seq = i2c_master_write_sequence::type_id::create("m_seq");
    s_seq = i2c_slave_read_sequence::type_id::create("s_seq");

    fork
      begin
        if(!m_seq.randomize() with {
          target_address == OTHER_BUSES;
          number_of_bytes == local::number_of_bytes;
          stop_condition == local::stop_condition;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(p_sequencer.m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
          foreach (local::ack_nack[i]) {
            data_ack_nack[i] dist {`ACK:=1, `NACK:=1};
          }
        })
        `uvm_fatal("RNDERR", "Failed to randomize slave sequence")
        s_seq.start(p_sequencer.s_seqr, this);
      end
    join
  endtask
