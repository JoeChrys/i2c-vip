class i2c_virtual_base_sequence extends uvm_sequence;
  `uvm_object_utils(i2c_virtual_base_sequence)
  `uvm_declare_p_sequencer(i2c_virtual_sequencer)

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
    soft (number_of_bytes < 8);
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
      s_seq.start(p_sequencer.s_seqr, this);
    end
  join
endtask

class i2c_virtual_sequence#(type MSEQ=i2c_master_base_sequence, type SSEQ=i2c_slave_base_sequence) extends i2c_virtual_base_sequence;
  `uvm_object_param_utils(i2c_virtual_sequence#(MSEQ, SSEQ))

  MSEQ m_seq;
  SSEQ s_seq;

  extern function new(string name = "i2c_virtual_sequence");
  extern virtual task body();
endclass

function i2c_virtual_sequence:: new(string name = "i2c_virtual_sequence");
  super.new(name);
endfunction // i2c_sequence::new

task i2c_virtual_sequence:: body();
  m_seq = MSEQ :: type_id :: create ("m_seq");
  s_seq = SSEQ :: type_id :: create ("s_seq");

  fork
    begin
      if (!m_seq.randomize() with {
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