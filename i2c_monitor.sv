
class i2c_monitor extends uvm_monitor; 
   
   `uvm_component_utils(i2c_monitor)

    virtual i2c_if                  i2c_vif;
   
    i2c_cfg                         cfg;
    i2c_item                        i2c_trans;
    i2c_coverage                    cov;

   
    uvm_analysis_port #(i2c_item)   i2c_mon_analysis_port;
    // uvm_analysis_port #(i2c_item)   i2c_s_analysis_port;

    bit                             transfer_done;
    bit                             cancel_first_bit;
    bit                             start_cond_from_prev_trans;
    
    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual task  run_phase(uvm_phase phase);  
    extern virtual task  do_monitor();

    extern virtual task  check_start_cond();
    extern virtual task  check_stop_cond();
    extern virtual task  check_data_transfer();

endclass // i2c_monitor_class

//-------------------------------------- 
//-----------------------------------------------------------------------
function i2c_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction   

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

  // if (cfg.has_coverage) begin
  //    cov = i2c_coverage::type_id::create("i2c_coverage",this);
  //    cov.cfg = this.cfg;
  // end  

  if (!cfg.has_checks)   
      `uvm_info("build_phase","CHECKERS DISABLED",UVM_LOW);
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
  end // of forever
      
endtask

task i2c_monitor::do_monitor();
  
  i2c_trans.start_condition = (start_cond_from_prev_trans) ? 'b1 : 'b0;
  
  cancel_first_bit = 'b0;
  start_cond_from_prev_trans = 'b0;

  fork
    check_start_cond();
    check_stop_cond();
    check_data_transfer();
  join_any
  disable fork;

  i2c_mon_analysis_port.write(i2c_trans); // sending sampled data to scoreboard
  // cov.i2c_cg.sample(i2c_trans); // sampling for coverage

  `uvm_info("Monitor", "do_monitor task executed", UVM_LOW)
endtask

task i2c_monitor::check_start_cond();
  forever begin
    `uvm_info("Monitor", "checking for start condition", UVM_DEBUG)
    @(negedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    // else ...
    start_cond_from_prev_trans = 'b1;  // already detected START, next one would be a repeated.

    // else if... (invalid/early start condition)
    if (!transfer_done) begin
      i2c_trans.transfer_failed = 'b1;
      `uvm_warning("Monitor", "Early START condition")
      break;  // break to exit and listen for next address
    end

    // else... (valid start condition)
    cancel_first_bit = 'b1;
    i2c_trans.start_condition = 'b1;

    `uvm_info("Monitor", "detected start condition", UVM_HIGH)
  end
endtask

task i2c_monitor::check_stop_cond();
  forever begin
    `uvm_info("Monitor", "checking for stop condition", UVM_DEBUG)
    @(posedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    // else if... 
      // if... (early/invalid stop condition)
    if (!transfer_done) begin
      i2c_trans.transfer_failed = 'b1;
      `uvm_warning("Monitor", "Early STOP condition")
    end

    i2c_trans.stop_condition = 'b1;

    `uvm_info("Monitor", "detected stop condition", UVM_HIGH)
    break; 
  end
endtask

task i2c_monitor::check_data_transfer();
  int bit_counter = 0;
  `uvm_info("Monitor", "checking for data transfer", UVM_DEBUG)

  while (bit_counter < 8) begin
    @(negedge i2c_vif.scl);

    if (cancel_first_bit) begin
      cancel_first_bit = 'b0;
      continue;
    end

    transfer_done = 'b0;
    i2c_trans.data[bit_counter] = i2c_vif.sda;
    bit_counter++;
    `uvm_info("Monitor", $sformatf("Got bit %1d with value %1b", bit_counter, i2c_trans.data[bit_counter]), UVM_DEBUG)
  end

  @(posedge i2c_vif.scl);   // not negedge at ack as slave driver can just release scl and not pulse it
  i2c_trans.ack_nack = i2c_vif.sda;
  `uvm_info("Monitor", "detected data transfer", UVM_HIGH)

  @(negedge i2c_vif.scl);   
  transfer_done = 'b1;

  // @(negedge i2c_vif.scl);   // delay task finish until negedge in case of STOP condition
endtask