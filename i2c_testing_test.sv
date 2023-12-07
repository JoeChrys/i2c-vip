/* 
    Test new code here, leave the poor i2c_random_test alone
*/

class i2c_testing_test extends i2c_base_test;

    `uvm_component_utils(i2c_testing_test)
    
    // rand int number_of_transactions;

    i2c_master_base_sequence m_seq;
        
    extern function new(string name = "i2c_testing_test", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void start_of_simulation_phase(uvm_phase phase);
    extern virtual task run_phase (uvm_phase phase);
    extern virtual function void report_phase(uvm_phase phase);
endclass 

//-------------------------------------------------------------------------------------------------------------
function i2c_testing_test::new(string name = "i2c_testing_test", uvm_component parent=null);    
    super.new(name,parent);
endfunction : new

//-------------------------------------------------------------------------------------------------------------
function void i2c_testing_test::build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    v_seq = i2c_master_base_sequence :: type_id :: create ("v_seq");
endfunction : build_phase

//-------------------------------------------------------------------------------------------------------------
function void i2c_testing_test::start_of_simulation_phase(uvm_phase phase);    
    super.start_of_simulation_phase(phase);    
endfunction

//-------------------------------------------------------------------------------------------------------------
task i2c_testing_test:: run_phase (uvm_phase phase);        
    super.run_phase(phase);
    phase.raise_objection(this);
    // number_of_transactions = $urandom_range(10,20);
    // number_of_transactions = 10;
   
    if (!v_seq.randomize() with {
      // add inline constraints here
    }) `uvm_fatal("RNDERR", "Virtual Sequence randomization failed")
    v_seq.start(null);

    #100;
    phase.drop_objection (this);
endtask
    
//---------------------------------------------------------------------------------------------------------------------
function void i2c_testing_test::report_phase(uvm_phase phase);
    super.report_phase(phase);
endfunction


