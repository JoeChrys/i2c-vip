
class i2c_monitor extends uvm_monitor; 
   
   `uvm_component_utils(i2c_monitor)

    virtual i2c_if i2c_vif;
   
    //i2c_coverage    cov;
    i2c_item   i2c_trans;

    i2c_cfg         cfg;
   
    uvm_analysis_port#(i2c_item)   i2c_mon_analysis_port;
    //uvm_analysis_port #(i2c_item)   i2c_s_analysis_port;

   
    bit reset_flag = 0;

    integer counter;
    bit first_start_condition;
    
    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual task  run_phase(uvm_phase phase);  
    extern virtual task  do_monitor();
    extern virtual task  reset_on_the_fly();

    extern virtual task  check_start_cond();
    extern virtual task  check_stop_cond();
    extern virtual task  check_data_transfer();
    
endclass // i2c_monitor_class

//-------------------------------------- 
//-----------------------------------------------------------------------
function i2c_monitor::new (string name, uvm_component parent);
    super.new(name, parent);
    i2c_trans = new();
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
 
    //if (cfg.has_coverage) begin
    //    cov = i2c_coverage::type_id::create("i2c_coverage",this);
    //    cov.cfg = this.cfg;
    //end  


    if (!cfg.has_checks)   
        `uvm_info("build_phase","CHECKERS DISABLED",UVM_LOW);
endfunction

//-------------------------------------------------------------------------------------------------------------
task  i2c_monitor::run_phase(uvm_phase phase);
    
	//wait for reset
	@(posedge i2c_vif.reset_n);
	repeat(3) @(posedge i2c_vif.system_clock);
    forever begin
      i2c_item i2c_trans = i2c_item::type_id::create("i2c_trans", this);
      // delete if bellow if UVC dosen't have reset on fly feature
    //   if (reset_flag) begin
    //         @(posedge i2c_vif.reset_n); // wait for reset to end
	//         repeat(3) @(posedge i2c_vif.system_clock); // wait 3 more clock cycles, just to be sure we're stable
    //         reset_flag = 0;
    //     end

        // fork 
            // reset_on_the_fly(); // delete this and fork if UVC dosen't have reset on fly feature
            do_monitor();
        // join_any
        // disable fork;
    end // of forever       
endtask


//-------------------------------------------------------------------------------------------------------------
task i2c_monitor::reset_on_the_fly();  
    // * * * Leave this untoched if planning to implement Reset on the fly feature. If not delete it. * * *   
    @(negedge i2c_vif.reset_n);
    reset_flag = 1;
    `uvm_info("MONITOR","ASYNCHRONOUS RESET HAPPENED", UVM_LOW)
    
endtask //reset_on_the_fly*/

task i2c_monitor::do_monitor();
    // * * * ADD SAMPLING LOGIC HERE * * *

    @(posedge i2c_vif.scl);  
    
    first_start_condition = 'b1;
    counter = 'b0;

    fork
        check_start_cond();
        check_stop_cond();
        check_data_transfer();
    join_any
    disable fork;

    `uvm_info("Monitor", "do_monitor task executed", UVM_LOW)
    //i2c_mon_analysis_port.write(i2c_trans); // sending sampled data to scoreboard
    //cov.i2c_cg.sample(i2c_trans); // sampling for coverage

endtask

task i2c_monitor::check_start_cond();
  forever begin
    `uvm_info("Monitor", "checking for start condition", UVM_DEBUG)
    @(negedge i2c_vif.sda)
    if (i2c_vif.scl == 1'b0) continue;

    if (!first_start_condition) begin
      i2c_mon_analysis_port.write(i2c_trans);
      break;  // break to exit and listen for next address
    end

    first_start_condition = 'b0;  // already detected START, next one would be a repeated.
    i2c_trans.start = 'b1;
    `uvm_info("Monitor", "detected start condition", UVM_HIGH)
  end
endtask

task i2c_monitor::check_stop_cond();
  forever begin
    `uvm_info("Monitor", "checking for stop condition", UVM_DEBUG)
    @(posedge i2c_vif.sda)
    if (i2c_vif.scl == 1'b0) continue;

    first_start_condition = 'b1;
    i2c_mon_analysis_port.write(i2c_trans);
    `uvm_info("Monitor", "detected stop condition", UVM_HIGH) 
  end
endtask

task i2c_monitor::check_data_transfer();
  `uvm_info("Monitor", "checking for data transfer", UVM_DEBUG)

  forever begin
    i2c_trans.data = new [counter + 1] (i2c_trans.data);
      for (int i = 7; i >= 0; i--) begin
        @(negedge i2c_vif.scl);
        i2c_trans.data[counter][i] = i2c_vif.sda;
        `uvm_info("Monitor", $sformatf("Got bit %1d with value %1b", i, i2c_trans.data[counter][i]), UVM_DEBUG)
      end
    @(posedge i2c_vif.scl);   // not negedge at ack as slave driver can just release scl and not pulse it
    i2c_trans.ack_nack = i2c_vif.sda;

    counter++;
    `uvm_info("Monitor", "detected data transfer", UVM_HIGH) 
  end 
endtask