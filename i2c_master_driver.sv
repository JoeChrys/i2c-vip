
class i2c_master_driver extends uvm_driver #(i2c_item);
  
  `uvm_component_utils(i2c_master_driver)

  virtual i2c_if    i2c_vif;
  
  i2c_cfg           cfg;
  i2c_item          rsp;

  bit               bus_busy;
  bit               transfer_aborted;

  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase (uvm_phase phase);
  extern virtual task  run_phase (uvm_phase phase);
  extern virtual task  do_init ();
  extern virtual task  reset_on_the_fly();
  extern virtual task  do_drive(i2c_item req);

  extern virtual task  do_start_cond();
  extern virtual task  do_stop_cond();
  extern virtual task  write_data();
  extern virtual task  check_data();
  extern virtual task  read_data();
  extern virtual task  send_bit(bit data_bit);
  extern virtual task  capture_bit(int index);
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

    do_drive(req);
  
    seq_item_port.item_done();
  end   // of forever
endtask // i2c_master_driver::run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_master_driver::do_init();
  i2c_vif.uvc_sda = 'bz;
  i2c_vif.uvc_scl = 'bz;
  @(posedge i2c_vif.system_clock);
  `uvm_info("Driver", "do_init task executed", UVM_LOW)
endtask // i2c_master_driver::do_init

task i2c_master_driver::do_drive(i2c_item req);
  bus_busy = (transfer_aborted) ? 'b1 : 'b0;  // check it previous transfer was aborted to toggle bus_busy flag
  transfer_aborted = 'b0;

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

  case (req.transaction_type)
  WRITE: begin  // begin-end block redundant (?)
          fork
            write_data();
            check_data();
          join
        end
  READ: read_data();
  endcase
    
  if (req.stop_condition && !transfer_aborted) begin
    do_stop_cond();
  end

  `uvm_info("Driver", "do_drive task executed", UVM_HIGH)
endtask // i2c_master_driver::do_drive
                                                                                // TODO refine timings
task i2c_master_driver::do_start_cond();
  if (i2c_vif.scl == 'b0) begin
    `uvm_info("Driver", "Preparing for Repeated START", UVM_HIGH)
    i2c_vif.uvc_sda = 'bz;
      assert (i2c_vif.sda == 'b1) 
      else   `uvm_error("Driver", "Expected SDA High but is Low")
    #5;
    i2c_vif.uvc_scl = 'bz;
      assert (i2c_vif.scl == 'b1) 
      else   `uvm_error("Driver", "Expected SCL High but is Low")
    #5;
  end

  `uvm_info("Driver", "Sending START", UVM_HIGH)
  i2c_vif.uvc_sda = 1'b0;
  #5;
  i2c_vif.uvc_scl = 1'b0;
endtask

task i2c_master_driver::do_stop_cond();
  assert (i2c_vif.scl == 'b0 && i2c_vif.sda == 'b0)
  else `uvm_error("Driver", "SDA or SCL unexpected HIGH")

  `uvm_info("Driver", "Sending STOP", UVM_HIGH)
  i2c_vif.uvc_scl = 1'bz;
  #5;
  i2c_vif.uvc_sda = 1'bz;
endtask

task i2c_master_driver::write_data();
  `uvm_info("Driver", "Master: Starting data transfer", UVM_HIGH)
  
  for (int i=7; i>=0; i--) begin
    if (transfer_aborted) return;
    `uvm_info("Driver", $sformatf("Sending bit %1d with value %1b", i, req.data[i]), UVM_DEBUG)
    fork
      send_bit(req.data[i]);
      pulse_clock();
    join
    `uvm_info("Driver", $sformatf("Sent bit %1d", i), UVM_HIGH)
  end
  `uvm_info("Driver", "Sent byte", UVM_HIGH)

  // pulse for ack/nack
  pulse_clock();

  `uvm_info("Driver", "Done sending data", UVM_HIGH)
endtask

task i2c_master_driver::check_data();
  for (int i=7; i>=0; i--) begin
    // @(posedge i2c_vif.scl) bit_correct = 'b0;  // in case of data clock stretching feature
    @(negedge i2c_vif.scl);  // could include the following it in a begin-end block
    rsp.data[i] = i2c_vif.sda;
    if (rsp.data[i] != req.data[i]) begin
      `uvm_warning("Driver", "Bit sent does NOT match SDA, aborting sequence...")
      transfer_aborted = 'b1;
      
      rsp.transfer_failed = 'b1;
      rsp.set_id_info(req);
      seq_item_port.put(rsp);
      return;
    end
    // else... (bit is correct)
  end
  @(posedge i2c_vif.scl);
  rsp.ack_nack = i2c_vif.sda;
  rsp.set_id_info(req);
  seq_item_port.put(rsp);

  case(rsp.ack_nack)
    `ACK:  `uvm_info("Driver", "Got ACK from slave", UVM_HIGH)
    `NACK: `uvm_warning("Driver", "Got NACK")
  endcase
endtask

task i2c_master_driver::read_data();
  `uvm_info("Driver", "Master: Reading data", UVM_HIGH)

  for (int bit_index=7; bit_index>=0; bit_index--) begin
    fork
      pulse_clock();
      capture_bit(bit_index);
    join
    `uvm_info("Driver", $sformatf("Got bit %1d with value %1b", bit_index, rsp.data[bit_index]), UVM_DEBUG)
  end
  //at this point seq should have set ack_nack
  fork
    send_bit(req.ack_nack);
    pulse_clock();
  join
  case(req.ack_nack)
    `ACK:  `uvm_info("Driver", "Sent ACK to slave", UVM_HIGH)
    `NACK: `uvm_warning("Driver", "Sent NACK")
  endcase
endtask

task i2c_master_driver::send_bit(bit data_bit);
  wait(i2c_vif.scl == 'b0);
  if (data_bit == 1) i2c_vif.uvc_sda = 'bz;
  else               i2c_vif.uvc_sda = data_bit;
  if (data_bit == 1) `uvm_info("Driver", "SDA was driven with Z", UVM_DEBUG)
  else               `uvm_info("Driver", "SDA was driven with 0", UVM_DEBUG)
endtask

task i2c_master_driver::capture_bit(int index);
  @(posedge i2c_vif.scl);  // or use begin-end block to control the order and sent rsp before the next pulse
  rsp.data[index] = i2c_vif.sda;

  // after reading the last bit, sent rsp to sequence
  if (index == 0) begin
    rsp.set_id_info(req);
    seq_item_port.put(rsp);
  end
endtask

task i2c_master_driver::pulse_clock();
  i2c_vif.uvc_scl = 'b0;                                                        // TODO Multiply delays by clock percentiles
  #5;
  i2c_vif.uvc_scl = 'bz;
  // wait in case slave is clock stretching
  wait (i2c_vif.scl == 'b1);
  #10;
  i2c_vif.uvc_scl = 0;
  #5;
endtask

/* 
 * This task executes the required item delay, it must be executed for the rest
 * of do_drive() to finish since it is the only task that returns, thus joining
 * the fork
 */
task i2c_master_driver::do_delay();
    `uvm_info("Driver", $sformatf("Waiting for %03d tu before sending", req.delay), UVM_HIGH)
    #(req.delay);                                                               // TODO Multiply by clock percentiles
    `uvm_info("Driver", "Done waiting (for item delay)", UVM_DEBUG)
endtask

/*
 * This task runs continuously until do_delay() is executed and flag bus_busy
 * is not set, then it is killed by 'disable fork'.
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
            `uvm_info("Driver", "External START condition detected, bus is busy, waiting...", UVM_LOW)
        end

        //STOP CONDITION
        begin
            @(posedge i2c_vif.sda) if (i2c_vif.scl == 1'b1);
            bus_busy = 0;
            `uvm_info("Driver", "External STOP condition detected, bus is now free", UVM_LOW)
        end
      join_any;
      disable fork;
  end
endtask

/*
 * This task runs continuously until do_delay() is executed and flag bus_busy
 * is not set, then it is killed by 'disable fork', or this task itself is executed.
 * It checks whether bus_busy flag has not been reset in a while and manually
 * resets it.
 */
task i2c_master_driver::bus_busy_timeout();                                     // TODO define bus_busy timeout according to default period (~100*clock_time)
  int i;
  wait (bus_busy);
  while(bus_busy) begin
    @(posedge i2c_vif.system_clock);  // ! change it to multiples of timing period
    i++;
    if (i > 20) begin   // ! 20->100
      `uvm_info("Driver", "TIMEOUT REACHED", UVM_LOW)
      bus_busy = 'b0;
      bus_busy_timeout();
    end
  end
endtask