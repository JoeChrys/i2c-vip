
class i2c_master_driver extends uvm_driver #(i2c_item);
    
    `uvm_component_utils(i2c_master_driver)
    virtual i2c_if   i2c_vif;
    
    i2c_cfg    cfg;
    bit reset_flag = 0;

    bit bus_busy = 0;

    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual task  run_phase (uvm_phase phase);
    extern virtual task  do_init ();
    extern virtual task  reset_on_the_fly();
    extern virtual task  do_drive(i2c_item req);

    extern virtual task  do_start_cond();
    extern virtual task  do_stop_cond();
    extern virtual task  transfer_data();
    extern virtual task  send_bit(bit data_bit);

    extern virtual task  do_delay();
    extern virtual task  check_bus_busy();
    
endclass // i2c_master_driver

//-------------------------------------------------------------------------------------------------------------
function i2c_master_driver::new(string name, uvm_component parent);
    super.new(name, parent);
endfunction // i2c_master_driver::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_master_driver::build_phase(uvm_phase phase);
    super.build_phase(phase); 
    `uvm_info("build_phase","BUILD i2c_MASTER_DRIVER",UVM_HIGH);
    if(!uvm_config_db#(virtual i2c_if)::get(this, "", "i2c_vif", i2c_vif)) 
        `uvm_fatal("build_phase",{"virtual interface must be set for: ", get_full_name(),".i2c_vif"});
    if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg)) begin
        `uvm_fatal("build_phase", "cfg wasn't set through config db");
    end
endfunction // i2c_master_driver::build_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_master_driver::run_phase(uvm_phase phase);
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
            // reset_on_the_fly(); // delete this and fork if UVC dosen't have reset on fly feature
            do_drive(req);
        join_any
        disable fork;
			
        seq_item_port.item_done();  

    end   // of forever
endtask// i2c_master_driver::run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_master_driver::do_init();
// * * * Write initial values for your signals here * * *
    @(posedge i2c_vif.system_clock);
    `uvm_info("Driver", "do_init task executed", UVM_LOW)
endtask

task i2c_master_driver::do_drive(i2c_item req);
// * * * Write driving logic here * * *
    // ! May need to add semaphore for multiple masters

    bus_busy = 0;

    fork
        do_delay();
        check_bus_busy();
    join_any

    wait (!bus_busy);
    disable fork;

    case (req.com_type)
        START: do_start_cond();
        STOP:  do_stop_cond();
        DATA:  transfer_data();
    endcase

    // @(posedge i2c_vif.system_clock);   
     `uvm_info("Driver", "do_drive task executed", UVM_HIGH)
endtask


task i2c_master_driver::reset_on_the_fly();
    // * * * Leave this untoched if planning to implement Reset on the fly feature. If not delete it. * * *
    @(negedge i2c_vif.reset_n);
    reset_flag = 1;
endtask

task i2c_master_driver::do_start_cond();
    `uvm_info("Driver", "Sending START", UVM_HIGH)
    i2c_vif.uvc_sda = 1'b0;
    i2c_vif.uvc_scl <= 1'b0;
    #5;
endtask

task i2c_master_driver::do_stop_cond();
    `uvm_info("Driver", "Sending STOP", UVM_HIGH)
    i2c_vif.uvc_scl = 1'bz;
    i2c_vif.uvc_sda <= 1'bz;
    #5;
endtask

task i2c_master_driver::transfer_data();
  `uvm_info("Driver", "Starting data transfer", UVM_HIGH)
  for (int i=7; i>=0; i--) begin
    `uvm_info("Driver", $sformatf("Sending bit %1d with value %1b", i, req.data[i]), UVM_DEBUG)
    i2c_vif.uvc_scl = 0;
    send_bit(req.data[i]);
    //pseudo clk with 0.5 duty cycle
    #5;
    i2c_vif.uvc_scl = 1'bz;
    #10;
    i2c_vif.uvc_scl = 0;
    #5;
    // end clock
    `uvm_info("Driver", $sformatf("Sent bit %1d", i), UVM_HIGH)
  end
    `uvm_info("Driver", "Done sending data", UVM_HIGH)
endtask

task i2c_master_driver::send_bit(bit data_bit);
  if (data_bit == 1) i2c_vif.uvc_sda = 1'bz;
  else               i2c_vif.uvc_sda = data_bit;
  if (data_bit == 1) `uvm_info("Driver", "SDA was driven with Z", UVM_DEBUG)
  else               `uvm_info("Driver", "SDA was driven with 0", UVM_DEBUG)
endtask

task i2c_master_driver::do_delay();
    `uvm_info("Driver", $sformatf("Waiting for %03d tu before sending", req.delay), UVM_HIGH)
    #(req.delay);
    `uvm_info("Driver", "Done waiting (for item delay)", UVM_DEBUG)
endtask

task i2c_master_driver::check_bus_busy();
    forever begin
        `uvm_info("Driver", "Checking if bus is busy...", UVM_DEBUG)
        //START CONDITION
        begin
            @(negedge i2c_vif.sda) if (i2c_vif.scl == 1'b1);
            bus_busy = 1;
            `uvm_info("Driver", "START condition detected, bus is busy, waiting...", UVM_LOW)
        end

        //STOP CONDITION
        begin
            @(posedge i2c_vif.sda) if (i2c_vif.scl == 1'b1);
            bus_busy = 0;
            `uvm_info("Driver", "STOP condition detected, bus is now free", UVM_LOW)
        end
    end
endtask

// TODO Add checks for each bit driven and remember to drive 1 with Z
// TODO eg if data[i] == i2c_vif.sda continue, else another driver is also sending