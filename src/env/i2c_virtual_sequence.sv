class i2c_virtual_base_sequence extends uvm_sequence;
  `uvm_object_utils(i2c_virtual_base_sequence)

  i2c_master_sequencer m_seqr;
  i2c_slave_sequencer s_seqr;

  i2c_cfg cfg;

  i2c_master_base_sequence m_seq;
  i2c_slave_base_sequence  s_seq;

  rand transaction_type_enum transaction_type;
  rand bit[7:0] data;
  rand bit      ack_nack;

  rand bit      start_condition;
  rand bit      stop_condition;
  rand bit      delay;

  rand int      clock_stretch_data[7:0];
  rand int      clock_stretch_ack;

  rand int      number_of_bytes;

  constraint c_virtual_defaults {
    soft (transaction_type == WRITE);
    soft (start_condition == 0);
    soft (stop_condition == 0);
    soft (delay == 0);
    soft (clock_stretch_ack == 0);
    foreach (clock_stretch_data[i]) {
      soft (clock_stretch_data[i] == 0);
    }
    number_of_bytes > 0;
    soft (number_of_bytes < 30);
  }

  extern function new(string name = "i2c_virtual_base_sequence");
  extern virtual task body();
endclass

  function i2c_virtual_base_sequence:: new(string name = "i2c_virtual_base_sequence");
    super.new(name);
  endfunction // i2c_sequence::new

  task i2c_virtual_base_sequence:: body();
    m_seq = i2c_master_base_sequence :: type_id :: create ("m_seq");
	  s_seq = i2c_slave_base_sequence :: type_id :: create ("s_seq");

    // could also use uvm_config_db
    // if (!uvm_config_db#(i2c_master_sequencer)::get(this,"","m_seqr", m_seqr) ) 
    //   `uvm_fatal("NULPTR", "Master Sequencer has not be set")
    // if (!uvm_config_db#(i2c_slave_sequencer)::get(this,"","s_seqr", s_seqr) ) 
    //  `uvm_fatal("NULPTR", "Slave Sequencer has not be set")
    if (m_seqr == null) `uvm_fatal("NULPTR", "Master Sequencer has not be set")
    if (s_seqr == null) `uvm_fatal("NULPTR", "Slave Sequencer has not be set")

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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          if (local::transaction_type == WRITE) transaction_type == READ;
          else if (local::transaction_type == READ) transaction_type == WRITE;
          data == local::data;
          ack_nack == local::ack_nack;
          clock_stretch_ack == local::clock_stretch_ack;
          foreach (local::clock_stretch_data[i]) {
            clock_stretch_data[i] == local::clock_stretch_data[i];
          }
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
    
    if (!uvm_config_db#(i2c_master_sequencer)::get(this,"","m_seqr", m_seqr) ) 
      `uvm_fatal("NULPTR", "Master Sequencer has not be set")
    if (!uvm_config_db#(i2c_slave_sequencer)::get(this,"","s_seqr", s_seqr) ) 
     `uvm_fatal("NULPTR", "Slave Sequencer has not be set")
     
    fork
      begin
        if(!m_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          number_of_bytes == local::number_of_bytes;
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
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
          s_seq.start(s_seqr, this);
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
        m_seq.start(m_seqr, this);
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
          s_seq.start(s_seqr, this);
        end
      end
    join
  endtask