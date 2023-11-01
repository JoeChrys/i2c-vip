
class i2c_slave_sequence extends uvm_sequence #(i2c_item);
 
    `uvm_object_utils(i2c_slave_sequence)
    `uvm_declare_p_sequencer(i2c_slave_sequencer)

    i2c_cfg cfg;

    // Item fields for Slave Seq
    rand transaction_type_enum transaction_type;
    rand bit[7:0] data;
    rand bit ack_nack;
    rand int clock_stretch_data[7:0];
    rand int clock_stretch_ack;

    // * * * Add constraints * * *
    constraint c_s_transaction_type { soft transaction_type == READ; }
    constraint c_s_clock_stretch { soft clock_stretch_ack == 0;
                                 foreach (clock_stretch_data[i]) 
                                    {soft clock_stretch_data[i] == 0;} }
    
    // constraint c_s_read_rsp { soft read_rsp == `ACK; }

    extern function new(string name = "i2c_slave_sequence");
    extern virtual task body();  
endclass // i2c_slave_sequence

//-------------------------------------------------------------------
function i2c_slave_sequence::new(string name = "i2c_slave_sequence");
    super.new(name);
endfunction //i2c_sequence::new

//-------------------------------------------------------------------
task i2c_slave_sequence::body();
    
    uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
    if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg",cfg))
        `uvm_fatal("body", "cfg wasn't set through config db");

	// * * * uvm_do or uvm_do_with can be used * * * 
    `uvm_do_with(req, { 
        transaction_type == local::transaction_type; 
        data == local::data;
        ack_nack == local::ack_nack;
        foreach (local::clock_stretch_data[i]) 
            {clock_stretch_data[i] == local::clock_stretch_data[i]};
        clock_stretch_ack == local::clock_stretch_ack;
        })
    `uvm_info("SLAVE SEQ", "WAITING FOR RSP", UVM_DEBUG)
    get_response(rsp);
    `uvm_info("SLAVE SEQ", "GOT RSP", UVM_DEBUG)
    if (transaction_type == READ) begin
    //   req.ack_nack = read_rsp;
    end

endtask