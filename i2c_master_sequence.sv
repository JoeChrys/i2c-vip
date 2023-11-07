class i2c_master_sequence extends uvm_sequence #(i2c_item);
 
    `uvm_object_utils(i2c_master_sequence)
    `uvm_declare_p_sequencer(i2c_master_sequencer)
    i2c_cfg cfg;

    // rand bit transfer_failed;

    // Item fields for Master Seq
    rand transaction_type_enum  transaction_type;
    rand bit[7:0]               data;
    rand bit                    ack_nack;
    rand bit                    start_condition;
    rand bit                    stop_condition;
    rand int                    delay;

    constraint c_m_transaction_type { soft transaction_type == WRITE; }
    constraint c_m_conditions       { soft start_condition == 0;
                                      soft stop_condition == 0; }
    constraint c_m_delay            { soft delay == 0; }

    // constraint c_read_rsp { soft read_rsp == `ACK; }
    
    extern function new(string name = "i2c_master_sequence");
    extern virtual task body();
    // extern function void pre_randomize(); 

endclass // i2c_master_sequence

//-------------------------------------------------------------------
function i2c_master_sequence:: new(string name = "i2c_master_sequence");
    super.new(name);
endfunction //i2c_sequence::new

//-------------------------------------------------------------------
task i2c_master_sequence:: body();
    
    uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
    if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg",cfg))
        `uvm_fatal("Master Sequence", "cfg wasn't set through config db");

	// * * * `uvm_do or `uvm_do_with can be used here * * * 
    // `uvm_do_with(req, { 
    //     transaction_type == local::transaction_type;
    //     data == local::data;
    //     ack_nack == local::ack_nack;
    //     start_condition == local::start_condition;
    //     stop_condition == local::stop_condition;
    //     delay == local::delay;
    //     })
    req = i2c_item::type_id::create("req");
    start_item(req);
    if ( !req.randomize() with { 
      transaction_type == local::transaction_type;
      data == local::data;
      ack_nack == local::ack_nack;
      start_condition == local::start_condition;
      stop_condition == local::stop_condition;
      delay == local::delay;
      } )
      `uvm_error("Master Sequence", "Sequence Randomization failed")
    finish_item(req);

    `uvm_info("MASTER SEQ", "WAITING FOR RSP", UVM_DEBUG)
    get_response(rsp);
    `uvm_info("MASTER SEQ", "GOT RSP", UVM_DEBUG)
    if (rsp.transfer_failed) begin
      // TODO
    end

	
endtask 

// function void i2c_master_sequence::pre_randomize();
//     super.pre_randomize();
// endfunction

class i2c_master_multibyte_sequence extends uvm_sequence #(i2c_item);
 
    `uvm_object_utils(i2c_master_multibyte_sequence)
    `uvm_declare_p_sequencer(i2c_master_sequencer)
    i2c_cfg cfg;

    // rand bit transfer_failed;
    rand int                    number_of_bytes;

    // Item fields for Master Seq
    rand transaction_type_enum  transaction_type;
    rand bit[7:0]               data[];
    rand bit                    ack_nack[];
    rand bit                    start_condition;
    rand bit                    stop_condition;
    rand int                    delay;

    constraint c_m_transaction_type { soft (transaction_type == WRITE); }
    constraint c_m_conditions       { soft (start_condition == 0);
                                      soft (stop_condition == 0); }
    constraint c_m_delay            { soft (delay == 0); }

    constraint c_m_nob              { number_of_bytes > 0;
                                      soft (number_of_bytes < 20); }
    constraint c_m_array_size       { data.size() == number_of_bytes;
                                      ack_nack.size() == number_of_bytes; }
    
    extern function new(string name = "i2c_master_multibyte_sequence");
    extern virtual task body();
    extern virtual task pre_randomize();

endclass // i2c_master_multibyte_sequence

//-------------------------------------------------------------------
function i2c_master_multibyte_sequence:: new(string name = "i2c_master_multibyte_sequence");
    super.new(name);
endfunction //i2c_sequence::new

//-------------------------------------------------------------------
task i2c_master_multibyte_sequence:: body();
    
    uvm_config_db#(i2c_cfg)::set(null, "*", "cfg", p_sequencer.cfg);
    if (!uvm_config_db#(i2c_cfg)::get(p_sequencer,"", "cfg", cfg))
        `uvm_fatal("Master Sequence", "cfg wasn't set through config db");

	// * * * `uvm_do or `uvm_do_with can be used here * * * 
    // `uvm_do_with(req, { 
    //     transaction_type == local::transaction_type;
    //     data == local::data;
    //     ack_nack == local::ack_nack;
    //     start_condition == local::start_condition;
    //     stop_condition == local::stop_condition;
    //     delay == local::delay;
    //     })
    for ( int i = 0; i < number_of_bytes; i++) begin
      req = i2c_item::type_id::create("req");
      start_item(req);
      if ( !req.randomize() with { 
        transaction_type == local::transaction_type;
        data == local::data[i];
        ack_nack == local::ack_nack[i];
        if (local::i == 0) {start_condition == local::start_condition;}
        if (local::i == number_of_bytes-1) {stop_condition == local::stop_condition;}
        delay == local::delay;
        } )
        `uvm_error("Master Sequence", $sformatf("Multibyte Sequence Randomization failed at %3d", i))
      finish_item(req);

      `uvm_info("MASTER SEQ", "WAITING FOR RSP", UVM_DEBUG)
      get_response(rsp);
      `uvm_info("MASTER SEQ", "GOT RSP", UVM_DEBUG)
      if (rsp.transfer_failed) begin
        // TODO
      end
    end

endtask 

task i2c_master_multibyte_sequence:: pre_randomize();
  `uvm_info("MASTER MB SEQ" "pre_randomize() called", UVM_DEBUG)
  // data = new[100];
  // ack_nack = new[100];
endtask