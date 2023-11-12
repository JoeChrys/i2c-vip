/* 
    Random test generates a random number (between 100 and 150) of transactions. And executes them.
*/


class i2c_random_test extends i2c_base_test;

    `uvm_component_utils(i2c_random_test)
    
    rand int number_of_transactions;

    i2c_master_base_sequence m_seq;
    i2c_slave_base_sequence s_seq;

    i2c_master_multibyte_sequence m_mb_seq;
    i2c_slave_multibyte_sequence s_mb_seq;

    i2c_master_write_sequence m_write_seq;
    i2c_slave_read_sequence s_read_seq;
        
    extern function new(string name = "i2c_random_test", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void start_of_simulation_phase(uvm_phase phase);
    extern virtual task run_phase (uvm_phase phase);
    extern virtual function void report_phase(uvm_phase phase);
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_random_test::new(string name = "i2c_random_test", uvm_component parent=null);    
    super.new(name,parent);
endfunction : new

//-------------------------------------------------------------------------------------------------------------
function void i2c_random_test::build_phase(uvm_phase phase);
    super.build_phase(phase);
  
	// m_seq = i2c_master_base_sequence :: type_id :: create ("m_seq");
	// s_seq = i2c_slave_sequence :: type_id :: create ("s_seq");

  m_mb_seq = i2c_master_multibyte_sequence::type_id::create("m_mb_seq");
  s_mb_seq = i2c_slave_multibyte_sequence::type_id::create("s_mb_seq");

  m_write_seq = i2c_master_write_sequence::type_id::create("m_write_seq");
  s_read_seq = i2c_slave_read_sequence::type_id::create("s_read_seq");

endfunction : build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_random_test::start_of_simulation_phase(uvm_phase phase);    
    super.start_of_simulation_phase(phase);    
endfunction

//-------------------------------------------------------------------------------------------------------------
task i2c_random_test:: run_phase (uvm_phase phase);        
    super.run_phase(phase);
    phase.raise_objection(this);
    // number_of_transactions = $urandom_range(5,10);
    fork
      begin
        if (!m_mb_seq.randomize() with {
          transaction_type == WRITE;
          start_condition == 1;
          stop_condition == 1;
        })
          `uvm_fatal("run_phase", "Rand err")
        m_mb_seq.start()
      end
      begin
        if (!s_mb_seq.randomize() with {
          transaction_type == READ;
        })
          `uvm_fatal("run_phase", "Rand err")
        m_mb_seq.start()
      end
    join
    #100
    phase.drop_objection (this);
endtask
    
//---------------------------------------------------------------------------------------------------------------------
function void i2c_random_test::report_phase(uvm_phase phase);
    super.report_phase(phase);
endfunction


