class i2c_virtual_base_sequence extends uvm_sequence;
  `uvm_object_utils(i2c_virtual_base_sequence)

  i2c_master_sequencer m_seqr;
  i2c_slave_sequencer s_seqr;

  i2c_cfg cfg;

  rand transaction_type_enum transaction_type;
  rand bit[7:0] data;
  rand bit      ack_nack;

  rand bit      start_condition;
  rand bit      stop_condition;
  rand bit      delay;

  rand int      clock_stretch_data[7:0];
  rand int      clock_stretch_ack;

  constraint c_virtual_defaults {
    soft (start_condition == 0);
    soft (stop_condition == 0);
    soft (delay == 0);
    soft (clock_stretch_ack == 0);
    foreach (clock_stretch_data[i]) {
      soft (clock_stretch_data[i] == 0);
    }
  }

  extern function new(string name = "i2c_virtual_base_sequence");
  extern virtual task body();
endclass

  function i2c_virtual_base_sequence:: new(string name = "i2c_virtual_base_sequence");
    super.new(name);
  endfunction // i2c_sequence::new

  function i2c_virtual_base_sequence:: body();
    m_seq = i2c_master_base_sequence :: type_id :: create ("m_seq");
	  s_seq = i2c_slave_base_sequence :: type_id :: create ("s_seq");

    // could also use uvm_config_db
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
          delay == local::delay
        })
        `uvm_fatal("RNDERR", "Failed to randomize master sequence")
        m_seq.start(m_seqr, this);
      end
      begin
        if (!s_seq.randomize() with {
          transaction_type == local::transaction_type;
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
  endfunction

