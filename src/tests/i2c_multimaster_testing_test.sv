class i2c_multimaster_testing_test extends i2c_multimaster_base_test;
  `uvm_component_utils(i2c_multimaster_testing_test)

  i2c_master_base_sequence m1_seq;
  i2c_master_base_sequence m2_seq;
  i2c_slave_base_sequence s_seq;

  extern function new(string name = "i2c_multimaster_testing_test", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
endclass // i2c_multimaster_testing_test

//-------------------------------------------------------------------------------------------------------------
function i2c_multimaster_testing_test:: new(string name = "i2c_multimaster_testing_test", uvm_component parent=null);
  super.new(name,parent);
endfunction // i2c_multimaster_testing_test::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_multimaster_testing_test:: build_phase(uvm_phase phase);
  super.build_phase(phase);

  m1_seq = i2c_master_base_sequence::type_id::create("m1_seq");
  m2_seq = i2c_master_base_sequence::type_id::create("m2_seq");
  s_seq = i2c_slave_base_sequence::type_id::create("s_seq");
endfunction // i2c_multimaster_testing_test::build_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_multimaster_testing_test:: run_phase(uvm_phase phase);
  super.run_phase(phase);
  phase.raise_objection(this);

  #(cfg.get_delay(FULL)*10);

  fork
    begin
      if (!m1_seq.randomize() with { 
          transaction_type == WRITE; 
          data == 8'h00; 
          ack_nack == `ACK; 
          start_condition == 1; 
          stop_condition == 1; 
          delay == 0; 
        }
      ) `uvm_error(get_type_name(), "Sequence Randomization failed")
      do begin
      m1_seq.start(env.v_seqr.m_seqr);
      end while (m1_seq.transfer_failed);
    end
    begin
      if (!m2_seq.randomize() with { 
          transaction_type == WRITE; 
          data == 8'hFF; 
          ack_nack == `ACK; 
          start_condition == 1; 
          stop_condition == 0; 
          delay == 1000; 
        }
      ) `uvm_error(get_type_name(), "Sequence Randomization failed")
      do begin
      m2_seq.start(env.v_seqr.m_seqr_2);
      end while (m2_seq.transfer_failed);
    end
    begin
      if (!s_seq.randomize() with {
          //constr
          transaction_type == READ;
        }
      ) `uvm_error(get_type_name(), "Sequence Randomization failed")
      repeat(2) s_seq.start(env.v_seqr.s_seqr);
    end
  join

  #(cfg.get_delay(FULL)*10);

  phase.drop_objection(this);
endtask // i2c_multimaster_testing_test::run_phase