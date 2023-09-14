
class i2c_slave_driver extends uvm_driver #(i2c_item);
    
    `uvm_component_utils(i2c_slave_driver)
    virtual i2c_if   i2c_vif;
    
    i2c_cfg    cfg;
    bit reset_flag = 0;

    bit bus_busy;

    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual task  run_phase (uvm_phase phase);
    extern virtual task  do_init ();
    extern virtual task  reset_on_the_fly();
    extern virtual task  do_drive(i2c_item req);

    extern virtual task  check_start_cond();
    extern virtual task  check_stop_cond();
    
endclass // i2c_slave_driver

//-------------------------------------------------------------------------------------------------------------
function i2c_slave_driver::new(string name, uvm_component parent);
    super.new(name, parent);
endfunction // i2c_slave_driver::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_slave_driver::build_phase(uvm_phase phase);
    super.build_phase(phase); 
    `uvm_info("build_phase","BUILD i2c_slave_DRIVER",UVM_HIGH);
    if(!uvm_config_db#(virtual i2c_if)::get(this, "", "i2c_vif", i2c_vif)) 
        `uvm_fatal("build_phase",{"virtual interface must be set for: ", get_full_name(),".i2c_vif"});
    if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg)) begin
        `uvm_fatal("build_phase", "cfg wasn't set through config db");
    end
endfunction // i2c_slave_driver::build_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_slave_driver::run_phase(uvm_phase phase);
    do_init();
	@(posedge i2c_vif.reset_n);
	repeat(3) @(posedge i2c_vif.system_clock);

	
    forever begin 
        seq_item_port.get_next_item(req);
        
        // delete if bellow if UVC dosen't have reset on fly feature 
        if (reset_flag) begin 
            @(posedge i2c_vif.reset_n); // wait for reset to end
	        repeat(3) @(posedge i2c_vif.system_clock); // wait 3 more clock cycles, just to be sure we're stable
            reset_flag = 0;
        end

        fork 
            reset_on_the_fly(); // delete this and fork if UVC dosen't have reset on fly feature
            do_drive(req);
        join_any
        disable fork;
			
        seq_item_port.item_done();  

    end   // of forever
endtask// i2c_slave_driver::run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_slave_driver::do_init();
// * * * Write initial values for your signals here * * *
    @(posedge i2c_vif.system_clock);  
    `uvm_info("Driver", "do_init task executed", UVM_LOW)
endtask

task i2c_slave_driver::do_drive(i2c_item req);
// * * * Write driving logic here * * *
    @(posedge i2c_vif.system_clock);  
     `uvm_info("Driver", "do_drive task executed", UVM_LOW)
endtask


task i2c_slave_driver::reset_on_the_fly();
    // * * * Leave this untoched if planning to implement Reset on the fly feature. If not delete it. * * *
    @(negedge i2c_vif.reset_n);
    reset_flag = 1;
endtask

task i2c_slave_driver::check_start_cond();
  forever begin
    `uvm_info("Driver", "checking for start condition", UVM_DEBUG)
    @(negedge i2c_vif.sda)
    if (i2c_vif.scl == 1'b0) continue; // not START condition

    `uvm_info("Driver", "detected start condition", UVM_HIGH)
  end
endtask

task i2c_slave_driver::check_stop_cond();

  forever begin
    `uvm_info("Driver", "checking for stop condition", UVM_DEBUG)
    @(posedge i2c_vif.sda)
    if (i2c_vif.scl == 1'b0) continue; // not STOP condition

    `uvm_info("Driver", "detected stop condition", UVM_HIGH) 
  end
endtask