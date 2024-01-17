class i2c_master_driver extends uvm_driver #(i2c_item);
  `uvm_component_utils(i2c_master_driver)

  virtual i2c_if    i2c_vif;
  
  i2c_cfg           cfg;

  bit               bus_busy;
  bit               transfer_aborted;
  int               bit_index;

  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase (uvm_phase phase);
  extern virtual task  run_phase (uvm_phase phase);
  extern virtual task  do_init ();
  extern virtual task  do_drive(i2c_item req);

  extern virtual task  do_start_cond();
  extern virtual task  do_stop_cond();
  extern virtual task  write_data();
  extern virtual task  check_data();
  extern virtual task  read_data();
  extern virtual task  send_bit(bit data_bit);
  extern virtual task  capture_bit(int index);
  extern virtual task  pulse_clock();
  extern virtual task  release_sda();

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
    seq_item_port.get(req);
    rsp = i2c_item::type_id::create("rsp");
    rsp.transaction_type = req.transaction_type;
    do_drive(req);
endtask // i2c_master_driver::run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_master_driver:: do_init();
  i2c_vif.uvc_sda = 'bz;
  i2c_vif.uvc_scl = 'bz;
  // @(posedge i2c_vif.system_clock);
  // `uvm_info("Driver", "do_init task executed", UVM_DEBUG)
endtask // i2c_master_driver::do_init

/*
 * This task executes the given item
 * It is the main task of the driver
 */
task i2c_master_driver:: do_drive(i2c_item req);
  bus_busy = (transfer_aborted) ? 'b1 : 'b0;  // check it previous transfer was aborted to toggle bus_busy flag
  transfer_aborted = 'b0;

  fork
    do_delay();
    check_bus_busy();
    //bus_busy_timeout();
  join_any

  if (bus_busy) begin
    `uvm_info("Driver", "Waiting for bus to be released", UVM_LOW)
    wait (!bus_busy);
    //delay below could be moved here
  end
  disable fork;

  #(cfg.get_delay());

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
  `uvm_info("Driver", "do_drive task executed", UVM_DEBUG)
endtask // i2c_master_driver::do_drive

/*
 * This task sends a START condition on the bus
 * If SCL is LOW, it sends a Repeated START condition
 */
task i2c_master_driver:: do_start_cond();
  if (i2c_vif.scl == 'b0) begin
    `uvm_info("Driver", "Preparing for Repeated START", UVM_HIGH)
    i2c_vif.uvc_sda = 'bz;
    #(cfg.get_delay());
    if (i2c_vif.sda != 'b1) `uvm_error("Driver", "Expected SDA High but is Low")
    i2c_vif.uvc_scl = 'bz;
    wait(i2c_vif.scl == 'b1);
    #(cfg.get_delay());
    if (i2c_vif.scl != 'b1) `uvm_error("Driver", "Expected SCL High but is Low")
  end

  `uvm_info("Driver", "Sending START", UVM_HIGH)
  i2c_vif.uvc_sda = 'b0;
  #(cfg.get_delay());
  i2c_vif.uvc_scl = 'b0;
  #(cfg.get_delay());
  if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg)) begin
    `uvm_fatal("run_phase", "cfg wasn't set through config db");
  end
endtask

/*
 * This task sends a STOP condition on the bus
 * It also does a preliminary check to see if SCL is HIGH which is unexpected
 */
task i2c_master_driver:: do_stop_cond();
  if (i2c_vif.scl != 'b0) `uvm_error("Driver", "SCL unexpected HIGH")

  i2c_vif.uvc_sda = 'b0;
  #(cfg.get_delay());

  `uvm_info("Driver", "Sending STOP", UVM_HIGH)
  i2c_vif.uvc_scl = 'bz;
  wait(i2c_vif.scl == 'b1);
  #(cfg.get_delay());
  i2c_vif.uvc_sda = 'bz;
  #(cfg.get_delay());
  if (i2c_vif.sda != 'b1) `uvm_error("Driver", "SDA unexpected LOW")
endtask

/*
 * This task sends data on the bus bit by bit
 * It runs in parallel with check_data() and is joined at the end
 */
task i2c_master_driver:: write_data();
  `uvm_info("Driver", "Master: Starting data transfer", UVM_HIGH)
  
  for (bit_index = 7; bit_index >= 0; bit_index--) begin
    if (transfer_aborted) return;
    `uvm_info("Driver", $sformatf("Sending bit %1d with value %1b", bit_index, req.data[bit_index]), UVM_DEBUG)
    send_bit(req.data[bit_index]);
    pulse_clock();
    `uvm_info("Driver", $sformatf("Bit %1d DONE\n", bit_index), UVM_HIGH)
  end
  `uvm_info("Driver", "Sent byte", UVM_HIGH)

  // release SDA for Slave to ACK/NACK
  release_sda();
  `uvm_info("Driver", "Released SDA for ACK", UVM_HIGH)

  // pulse for ack/nack
  fork
    if (req.data == START_BYTE) begin
      `uvm_info(get_type_name(), "Sent START BYTE, doing self-ACK", UVM_LOW)
      send_bit(`ACK);
    end
    pulse_clock();
    begin
      @(posedge i2c_vif.scl);
      rsp.ack_nack = i2c_vif.sda;
      rsp.set_id_info(req);
      seq_item_port.put(rsp);
    end
  join
  `uvm_info("Driver", "Done sending data", UVM_HIGH)
endtask

/*
 * This task checks the data sent by the master itself
 * It runs in parallel with write_data() and is joined at the end
 */
task i2c_master_driver:: check_data();
  @(posedge i2c_vif.scl);
  for (int i=7; i>=0; i--) begin
    @(negedge i2c_vif.scl);
    rsp.data[i] = i2c_vif.sda;
    `uvm_info("Driver", $sformatf("Bit %1d has value: %1b", i, rsp.data[i]), UVM_DEBUG)
    if (rsp.data[i] != req.data[i]) begin
      `uvm_warning("Driver", $sformatf("Bit sent (%1b) does NOT match SDA, aborting sequence...", rsp.data[i]))
      transfer_aborted = 'b1;
      rsp.transfer_failed = 'b1;
      rsp.set_id_info(req);
      seq_item_port.put(rsp);
      return;
    end
    // else... (bit is correct)
  end

  @(negedge i2c_vif.scl);
  case(rsp.ack_nack)
    `ACK:  `uvm_info("Driver", "Got ACK from slave", UVM_HIGH)
    `NACK: `uvm_info("Driver", "Got NACK", UVM_LOW)
  endcase
endtask

/*
 * This task reads data from the bus bit by bit, also does ACK/NACK at the end
 */
task i2c_master_driver:: read_data();
  `uvm_info("Driver", "Master: Reading data", UVM_HIGH)

  for (bit_index = 7; bit_index >= 0; bit_index--) begin
    fork
      pulse_clock();
      capture_bit(bit_index);
    join
    // May need to include it in fork in case of race conditions
    if (bit_index == 0) begin
      rsp.set_id_info(req);
      seq_item_port.put(rsp);
    end
  end
  //at this point seq should have set ack_nack
  send_bit(req.ack_nack);
  pulse_clock();
  release_sda();
  case(req.ack_nack)
    `ACK:  `uvm_info("Driver", "Sent ACK to slave", UVM_HIGH)
    `NACK: `uvm_info("Driver", "Sent NACK", UVM_LOW)
  endcase
endtask

/*
 * This task sends a bit on the bus
 * It also does a preliminary check to see if SCL is HIGH which is unexpected
 */
task i2c_master_driver:: send_bit(bit data_bit);
  if (i2c_vif.scl != 'b0) `uvm_error("Driver", "SCL unexpected HIGH")
  if (data_bit == 1) i2c_vif.uvc_sda = 'bz;
  else               i2c_vif.uvc_sda = data_bit;
  if (data_bit == 1) `uvm_info("Driver", "SDA was driven with Z", UVM_DEBUG)
  else               `uvm_info("Driver", "SDA was driven with 0", UVM_DEBUG)
endtask

/*
 * This task captures the bit at the given index and stores it in rsp
 * I2C controllers are supposed to sample on the bus to compare with the bit sent
 */
task i2c_master_driver:: capture_bit(int index);
  @(posedge i2c_vif.scl);  // or use begin-end block to control the order and sent rsp before the next pulse
  rsp.data[index] = i2c_vif.sda;
  `uvm_info("Driver", $sformatf("Got bit %1d with value %1b", bit_index, rsp.data[bit_index]), UVM_DEBUG)
endtask

/*
 * This task pulses the clock, it must be executed for the rest of do_drive() to finish since it is the only task that returns, thus joining the fork
 * "wait (i2c_vif.scl == 'b1);" is used to wait for slave to release clock stretching
 */
task i2c_master_driver:: pulse_clock();
  i2c_vif.uvc_scl = 'b0;
  #(cfg.get_delay());
  i2c_vif.uvc_scl = 'bz;
  // wait in case slave is clock stretching
  wait (i2c_vif.scl == 'b1);
  #(cfg.get_delay(HALF));
  i2c_vif.uvc_scl = 'b0;
  #(cfg.get_delay());
endtask

/*
 * This task releases SDA also does a preliminary check to see if SCL is HIGH which is unexpected
 */
task i2c_master_driver:: release_sda();
  if (i2c_vif.scl == 'b1) `uvm_error("Driver", "SCL unexpected HIGH when releasing SDA")
  i2c_vif.uvc_sda = 'bz;
endtask

/* 
 * This task executes the required item delay, it must be executed for the rest
 * of do_drive() to finish since it is the only task that returns, thus joining
 * the fork
 */
task i2c_master_driver:: do_delay();
    `uvm_info("Driver", $sformatf("Waiting for %03d tu before sending", req.delay), UVM_HIGH)
    #(req.delay*cfg.get_delay(QUANTUM));
    `uvm_info("Driver", "Done waiting (for item delay)", UVM_DEBUG)
endtask

/*
 * This task runs continuously until do_delay() is executed and flag bus_busy
 * is not set, then it is killed by 'disable fork'.
 * It checks for START/STOP conditions and alters the bus_busy flag accordingly
 */
task i2c_master_driver:: check_bus_busy();
  fork
    forever begin : DETECT_START
      @(negedge i2c_vif.sda);
      if (i2c_vif.scl == 'b0) continue;
      bus_busy = 1;
      `uvm_warning("Driver", "External START condition detected, bus is busy, waiting...")
    end
    forever begin
      @(posedge i2c_vif.sda);
      if (i2c_vif.scl == 'b0) continue;
      bus_busy = 0;
      `uvm_info("Driver", "External STOP condition detected, bus is now free", UVM_LOW)
    end
  join_any
  `uvm_error("Driver", "Execution should not reach this point")
endtask

/*
 * This task runs continuously until do_delay() is executed and flag bus_busy
 * is not set, then it is killed by 'disable fork', or this task itself is executed.
 * It checks whether bus_busy flag has not been reset in a while and manually
 * resets it.
 */
task i2c_master_driver:: bus_busy_timeout();
  int i;

  wait (bus_busy);
  while(bus_busy) begin
    #(cfg.get_delay(FULL));
    i++;
    if (i > 10) begin
      `uvm_info("Driver", "TIMEOUT REACHED", UVM_LOW)
      if (i2c_vif.sda == 'b1 && i2c_vif.scl == 'b1) begin
        `uvm_info("Driver", "Manually resetting bus_busy flag", UVM_LOW)
        bus_busy = 'b0;
        break;
      end
      bus_busy_timeout();
    end
  end
endtask