class i2c_master_sequence extends uvm_sequence #(i2c_item);
 
    `uvm_object_utils(i2c_master_sequence)
    `uvm_declare_p_sequencer(i2c_master_sequencer)
    i2c_cfg cfg;

    rand bit read_rsp;
    rand bit transfer_failed;
    rand bit require_ack_rsp;

    constraint c_read_rsp { soft read_rsp == `ACK; }
    constraint c_transfer_failed { soft transfer_failed == 'b0; }
    
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
        `uvm_fatal("Master Sequence", "cfg wasn't set through config db");

	// * * * `uvm_do or `uvm_do_with can be used here * * * 
    start_item(req);
    if ( !req.randomize() )
      `uvm_fatal("Master Sequence", "req randomization failed");
    finish_item(req);
    get_response(rsp);
    if (req.transaction_type == READ) begin
      req.ack_nack = read_rsp;
    end

	
endtask 


