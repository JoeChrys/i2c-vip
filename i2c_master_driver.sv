
class i2c_master_driver extends uvm_driver #(i2c_item);
    
    `uvm_component_utils(i2c_master_driver)
    virtual i2c_if    i2c_vif;
    
    i2c_cfg           cfg;
    bit               reset_flag = 0;

    bit               bus_busy;
    bit               previous_transfer_aborted;

    i2c_item          rsp;

    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual task  run_phase (uvm_phase phase);
    extern virtual task  do_init ();
    extern virtual task  reset_on_the_fly();
    extern virtual task  do_drive(i2c_item req);

    extern virtual task  do_start_cond();
    extern virtual task  do_stop_cond();
    extern virtual task  write_data();
    extern virtual task  listen_data();
    extern virtual task  send_bit(bit data_bit);
    extern virtual task  pulse_clock();

    extern virtual task  do_delay();
    extern virtual task  check_bus_busy();
    extern virtual task  bus_busy_timeout();
    
endclass // i2c_master_driver

//-------------------------------------------------------------------------------------------------------------
function i2c_master_driver::new(string name, uvm_component parent);
    super.new(name, parent);
endfunction // i2c_master_driver::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_master_driver::build_phase(uvm_phase phase);
    super.build_phase(phase); 
    `uvm_info("build_phase","BUILD I2C_MASTER_DRIVER",UVM_HIGH);
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
        rsp = i2c_item::type_id::create("rsp");
        
        // delete if bellow if UVC dosen't have reset on fly feature 
        if (reset_flag) begin 
            @(posedge i2c_vif.reset_n); // wait for reset to end
	        repeat(3) @(posedge i2c_vif.system_clock); // wait 3 more clock cycles, just to be sure we're stable
            reset_flag = 0;
        end

        //bus_busy timeout ~100clocks

        fork 
            // reset_on_the_fly(); // delete this and fork if UVC dosen't have reset on fly feature
            do_drive(req);
        join_any
        disable fork;
			
        seq_item_port.item_done(rsp);

    end   // of forever
endtask // i2c_master_driver::run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_master_driver::do_init();
// * * * Write initial values for your signals here * * *
    @(posedge i2c_vif.system_clock);
    `uvm_info("Driver", "do_init task executed", UVM_LOW)
endtask // i2c_master_driver::do_init

task i2c_master_driver::do_drive(i2c_item req);
// * * * Write driving logic here * * *

    bus_busy = (previous_transfer_aborted) ? 1 : 0;
    previous_transfer_aborted = 'b0;

    fork
        do_delay();
        check_bus_busy();
        //bus_busy_timeout();
    join_any

    wait (!bus_busy);
    disable fork;

    if (req.start_condition) begin
      do_start_cond();
    end

    fork
      write_data();
      listen_data();
    join_any
    disable fork;
      
    if (req.stop_condition && !previous_transfer_aborted) begin
      do_stop_cond();
    end

    // @(posedge i2c_vif.system_clock);   
     `uvm_info("Driver", "do_drive task executed", UVM_HIGH)
endtask // i2c_master_driver::do_drive


task i2c_master_driver::reset_on_the_fly();
    // * * * Leave this untoched if planning to implement Reset on the fly feature. If not delete it. * * *
    @(negedge i2c_vif.reset_n);
    reset_flag = 1;
endtask

// ! refine timings
task i2c_master_driver::do_start_cond();
    `uvm_info("Driver", "Sending START", UVM_HIGH)
    i2c_vif.uvc_sda = 1'b0;
    #5;
    i2c_vif.uvc_scl = 1'b0;
endtask

task i2c_master_driver::do_stop_cond();
    `uvm_info("Driver", "Sending STOP", UVM_HIGH)
    i2c_vif.uvc_scl = 1'bz;
    #5;
    i2c_vif.uvc_sda = 1'bz;
endtask

task i2c_master_driver::write_data();
  `uvm_info("Driver", "Starting data transfer", UVM_HIGH)
  
  foreach (req.data[i]) begin
    for (int j=7; j>=0; j--) begin
      `uvm_info("Driver", $sformatf("Sending bit %1d with value %1b", j, req.data[i][j]), UVM_DEBUG)
      fork
        send_bit(req.data[i][j]);
        pulse_clock();
      join
      `uvm_info("Driver", $sformatf("Sent bit %1d", j), UVM_HIGH)
    end
    `uvm_info("Driver", "Sent byte", UVM_HIGH)

    // pulse for ack/nack
    fork
      pulse_clock();
      @(posedge i2c_vif.scl); // in case of slave clock stretching
    join
  end
    
  `uvm_info("Driver", "Done sending data", UVM_HIGH)
endtask

task i2c_master_driver::listen_data();
  foreach (req.data[i]) begin
    for (int j=7; j>=0; j--) begin
      @(posedge i2c_vif.scl);
      rsp.data[i][j] = i2c_vif.sda;
      if (rsp.data[i][j] != req.data[i][j]) begin
        `uvm_warning("Driver", "Bit sent does NOT match SDA, aborting sequence...")
        rsp.ack_nack = `NACK;
        previous_transfer_aborted = 'b1;
        return;
      end
    end
    @(posedge i2c_vif.scl);
    rsp.ack_nack = i2c_vif.sda;

    case(rsp.ack_nack)
        `ACK:  `uvm_info("Driver", "Got ACK from slave", UVM_HIGH)
        `NACK: `uvm_warning("Driver", "Got NACK")
    endcase
  end
  return;
endtask

task i2c_master_driver::send_bit(bit data_bit);
  wait(i2c_vif.scl == 'b0);
  if (data_bit == 1) i2c_vif.uvc_sda = 'bz;
  else               i2c_vif.uvc_sda = data_bit;
  if (data_bit == 1) `uvm_info("Driver", "SDA was driven with Z", UVM_DEBUG)
  else               `uvm_info("Driver", "SDA was driven with 0", UVM_DEBUG)
endtask

task i2c_master_driver::pulse_clock();
  i2c_vif.uvc_scl = 'b0;
  // ! Multiply delays by clock percentiles
  #5;
  i2c_vif.uvc_scl = 1'bz;
  #10;
  i2c_vif.uvc_scl = 0;
  #5;
endtask

task i2c_master_driver::do_delay();
    `uvm_info("Driver", $sformatf("Waiting for %03d tu before sending", req.delay), UVM_HIGH)
    #(req.delay); // ! Multiply by clock percentiles
    `uvm_info("Driver", "Done waiting (for item delay)", UVM_DEBUG)
endtask

/*
 * This task runs continuously until do_delay() is executed and flag bus_busy
 * is not set, then it is killed by disable_fork.
 * It checks for START/STOP conditions and alters the bus_busy flag accordingly
 */
task i2c_master_driver::check_bus_busy();
  forever begin
      `uvm_info("Driver", "Checking if bus is busy...", UVM_DEBUG)
      fork
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
      join_any;
      disable fork;
  end
endtask

/*
 * This task runs continuously until do_delay() is executed and flag bus_busy
 * is not set, then it is killed by disable_fork, or this task itself is executed.
 * It checks whether bus_busy flag has not been reset in a while and manually
 * resets it.
 */
task i2c_master_driver::bus_busy_timeout();
  integer i;
  wait (bus_busy);
  while(bus_busy) begin
    @(posedge i2c_vif.system_clock);  // ! change it to multiples of timing period
    i++;
    if (i > 20) begin
      bus_busy = 'b0;
      bus_busy_timeout();
    end
  end
endtask