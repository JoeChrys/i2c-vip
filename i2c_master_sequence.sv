class i2c_master_sequence extends uvm_sequence #(i2c_item);
 
    `uvm_object_utils(i2c_master_sequence)
    `uvm_declare_p_sequencer(i2c_master_sequencer)
    i2c_cfg cfg;

    rand bit read_rsp;
    // rand bit transfer_failed;
    // rand bit require_ack_rsp;

    // Item fields for Master Seq
    rand transaction_type_enum transaction_type;
    rand bit[7:0] data;
    // rand bit ack_nack;
    rand bit start_condition;
    rand bit stop_condition;
    rand int delay;

    constraint c_m_transaction_type { soft transaction_type == WRITE; }
    constraint c_m_conditions       { soft start_condition == 0;
                                      soft stop_condition == 0; }
    constraint c_m_delay            { soft delay == 0; }

    constraint c_read_rsp { soft read_rsp == `ACK; }
    
    extern function new(string name = "i2c_master_sequence");
    extern virtual task body();
    // extern function void pre_randomize(); 

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
    `uvm_do_with(req, { 
        transaction_type == local::transaction_type;
        data == local::data;
        // ack_nack == local::ack_nack;
        start_condition == local::start_condition;
        stop_condition == local::stop_condition;
        delay == local::delay;
        })
    `uvm_info("MASTER SEQ", "WAITING FOR RSP", UVM_DEBUG)
    get_response(rsp);
    `uvm_info("MASTER SEQ", "GOT RSP", UVM_DEBUG)
    if (transaction_type == READ) begin
      req.ack_nack = read_rsp;
      `uvm_info("MASTER SEQ", $sformatf("SET ACK to %1b", read_rsp), UVM_DEBUG)
    end

	
endtask 

// function void i2c_master_sequence::pre_randomize();
//     super.pre_randomize();
// endfunction