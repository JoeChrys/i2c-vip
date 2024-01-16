class i2c_monitor extends uvm_monitor; 
  `uvm_component_utils(i2c_monitor)

  uvm_analysis_port #(i2c_item)   i2c_mon_analysis_port;

  virtual i2c_if                  i2c_vif;
  i2c_cfg                         cfg;
  i2c_item                        i2c_trans;
  
  int                             bit_counter;
  bit                             start_cond_from_prev_trans;
  bit                             captured_next_msb;
  bit                             msb;

  bit                             transfer_done;
  bit                             bus_active;
  
  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase (uvm_phase phase);
  extern virtual task  run_phase(uvm_phase phase);  
  extern virtual task  do_monitor();

  extern virtual task  check_start_cond();
  extern virtual task  check_stop_cond();
  extern virtual task  check_data_transfer();
endclass // i2c_monitor_class

//-----------------------------------------------------------------------
function i2c_monitor:: new (string name, uvm_component parent);
  super.new(name, parent);
endfunction // i2c_monitor::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  `uvm_info("build_phase","BUILD i2c_MONITOR",UVM_MEDIUM);
  if(!uvm_config_db#(virtual i2c_if)::get(this, "", "i2c_vif", i2c_vif)) 
    `uvm_fatal("build_phase",{"virtual interface must be set for: ",get_full_name(),".i2c_vif"});

  if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg",cfg)) begin
    `uvm_fatal("build_phase", "cfg wasn't set through config db");
  end

  i2c_mon_analysis_port = new("i2c_mon_analysis_port",this);
endfunction

//-------------------------------------------------------------------------------------------------------------
task  i2c_monitor::run_phase(uvm_phase phase);
	//wait for reset
	@(posedge i2c_vif.reset_n);
	repeat(3) @(posedge i2c_vif.system_clock);
  
  transfer_done = 'b1;

  forever begin
    i2c_trans = new();
    do_monitor();
  end       
endtask

task i2c_monitor::do_monitor();
  if (start_cond_from_prev_trans) i2c_trans.start_condition = 'b1;
  start_cond_from_prev_trans = 'b0;

  fork
    check_start_cond();
    check_stop_cond();
    check_data_transfer();
  join_any
  disable fork;

  i2c_mon_analysis_port.write(i2c_trans);

  `uvm_info("Monitor", "do_monitor task executed", UVM_DEBUG)
endtask

task i2c_monitor::check_start_cond();
  forever begin
    // `uvm_info("Monitor", "checking for start condition", UVM_DEBUG)
    @(negedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    `uvm_info("Monitor", "detected start condition", UVM_HIGH)

    // else if... (invalid/early start condition)
    if (!transfer_done) begin
      i2c_trans.transfer_failed = 'b1;
      start_cond_from_prev_trans = 'b1;
      `uvm_error("Monitor", "Early START condition")
      break;  // break to exit and listen for next address
    end

    // else if ... (repeated Start Condition)
    if (bus_active == 'b1) begin
      start_cond_from_prev_trans = 'b1;  // already detected START, next one would be a repeated.
      break;
    end

    // else... (valid start condition)
    i2c_trans.start_condition = 'b1;
    bus_active = 'b1;
  end
endtask

task i2c_monitor::check_stop_cond();
  forever begin
    // `uvm_info("Monitor", "checking for stop condition", UVM_DEBUG)
    @(posedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    // else if... 
      // if... (early/invalid stop condition)
    if (!transfer_done) begin
      i2c_trans.transfer_failed = 'b1;
      `uvm_error("Monitor", "Early STOP condition")
    end

    i2c_trans.stop_condition = 'b1;
    bus_active = 'b0;

    `uvm_info("Monitor", "detected stop condition", UVM_HIGH)
    break; 
  end
endtask

task i2c_monitor::check_data_transfer();
  bit_counter = 0;
  `uvm_info("Monitor", "checking for data transfer", UVM_DEBUG)

  while (bit_counter < 8) begin
    // if previous task call captured current MSB, retrieve it (only enters at bit_counter == 0)
    if (captured_next_msb) begin
      if (bit_counter != 0) `uvm_fatal("Monitor", "Unexpected behavior")

      captured_next_msb = 0;
      i2c_trans.data[`rev_put(bit_counter)] = msb;
      bit_counter++;
      continue;
    end

    @(posedge i2c_vif.scl);
    i2c_trans.data[`rev_put(bit_counter)] = i2c_vif.sda;
    `uvm_info("Monitor", $sformatf("(posedge) Bit %1d has value: %b", `rev_put(bit_counter), i2c_vif.sda), UVM_DEBUG)

    @(negedge i2c_vif.scl);
    `uvm_info("Monitor", $sformatf("(negedge) Bit %1d has value: %b", `rev_put(bit_counter), i2c_vif.sda), UVM_DEBUG)
    // if ... (first negedge SCL is Start Condition, skip bit)
    if (i2c_vif.sda != i2c_trans.data[`rev_put(bit_counter)]) begin
      // if (bit_counter == 0) continue;

      // else ...
      `uvm_error("Monitor", "Detected Start/Stop Condition, not Data bit")
    end

    transfer_done = 'b0; // at this point data transfer has begun
    i2c_trans.data[`rev_put(bit_counter)] = i2c_vif.sda;
    `uvm_info("Monitor", $sformatf("Got bit %1d with value %1b", 7-bit_counter, i2c_trans.data[7-bit_counter]), UVM_DEBUG)
    bit_counter++;
  end

  @(posedge i2c_vif.scl);   
  i2c_trans.ack_nack = i2c_vif.sda;
  `uvm_info("Monitor", $sformatf("(posedge) ACK_NACK: %b", i2c_vif.sda), UVM_DEBUG)

  @(negedge i2c_vif.scl);
  `uvm_info("Monitor", $sformatf("(negedge) ACK_NACK: %b", i2c_vif.sda), UVM_DEBUG)
  if (i2c_vif.sda != i2c_trans.ack_nack) begin
    `uvm_error("Monitor", "Detected Start/Stop Condition, not ACK bit")
  end

  transfer_done = 'b1;
  `uvm_info("Monitor", "Detected data transfer (byte)", UVM_HIGH)

  bit_counter++;
  @(posedge i2c_vif.scl);
  msb = i2c_vif.sda;
  `uvm_info("Monitor", $sformatf("(posedge) Next byte MSB has value: %b", i2c_vif.sda), UVM_DEBUG)

  @(negedge i2c_vif.scl);
  `uvm_info("Monitor", $sformatf("(negedge) Next byte MSB has value: %b", i2c_vif.sda), UVM_DEBUG)

  if (i2c_vif.sda != msb) `uvm_fatal("Monitor", "Expected data item to be finished by now")

  captured_next_msb = 'b1;
  transfer_done = 'b0;
endtask