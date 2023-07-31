class i2c_master_sequence extends uvm_sequence #(i2c_item);
 
    `uvm_object_utils(i2c_master_sequence)
    `uvm_declare_p_sequencer(i2c_master_sequencer)
    i2c_cfg cfg;
    
    extern function new(string name = "i2c_master_sequence");
    extern virtual task body();   

endclass // i2c_master_sequence

//-------------------------------------------------------------------
function i2c_master_sequence::new(string name = "i2c_master_sequence");
    super.new(name);
endfunction //i2c_sequence::new

//-------------------------------------------------------------------
task i2c_master_sequence::body();
    
    uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
    if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg",cfg))
        `uvm_fatal("body", "cfg wasn't set through config db");

	// * * * `uvm_do or `uvm_do_with can be used here * * * 
    `uvm_do(req)
	
endtask 


