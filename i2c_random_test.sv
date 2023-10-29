/* 
    Random test generates a random number (between 100 and 150) of transactions. And executes them.
*/


class i2c_random_test extends i2c_base_test;

    `uvm_component_utils(i2c_random_test)
    
    rand int number_of_transactions;


    i2c_master_sequence m_seq;
    i2c_slave_sequence s_seq;
        
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
  
	m_seq = i2c_master_sequence :: type_id :: create ("m_seq");
	s_seq = i2c_slave_sequence :: type_id :: create ("s_seq");

endfunction : build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_random_test::start_of_simulation_phase(uvm_phase phase);    
    super.start_of_simulation_phase(phase);    
endfunction

//-------------------------------------------------------------------------------------------------------------
task i2c_random_test:: run_phase (uvm_phase phase);        
    super.run_phase(phase);
    phase.raise_objection(this);
    number_of_transactions = $urandom_range(3,5);
    for (int i = 0; i < number_of_transactions; i++) begin
        fork
            begin
                if (!m_seq.randomize() with {                     
                    transaction_type == WRITE;
                    delay inside {[25:30]};
                    start_condition == 1;
                    stop_condition == 1;             
                })
                `uvm_fatal("run_phase","i2c_master_sequence randomization failed"); 
                m_seq.start(env.master_agent.m_seqr);
            end 
            begin
                if (!s_seq.randomize() with { 
				    transaction_type == READ;
                    clock_stretch_ack inside {[25:30]};
                    ack_nack dist { `ACK:=5, `NACK:=1 };
                    foreach (clock_stretch_data[i]) clock_stretch_data[i] inside {[25:30]};
                })
                `uvm_fatal("run_phase","i2c_slave_sequence randomization failed");        
                s_seq.start(env.slave_agent.s_seqr);
            end                
        join
    end
    #100;
    phase.drop_objection (this);
endtask
    
//---------------------------------------------------------------------------------------------------------------------
function void i2c_random_test::report_phase(uvm_phase phase);
    super.report_phase(phase);
endfunction


