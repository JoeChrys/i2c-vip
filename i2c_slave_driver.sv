
class i2c_slave_driver extends uvm_driver #(i2c_item);
    
    `uvm_component_utils(i2c_slave_driver)

    virtual i2c_if          i2c_vif;

    i2c_cfg                 cfg;

    bit                     enable;
    int                     bit_index;
    bit                     counter_reset;
    bit                     transfer_done;

    slave_driver_type_enum  slave_driver_type = PERIPHERAL_DEVICE;              // TODO make it change in build_phase via cfg

    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual task  run_phase (uvm_phase phase);
    extern virtual task  do_init();
    extern virtual task  do_drive();

    extern virtual task  detect_start_cond();
    extern virtual task  detect_stopt_cond();
    extern virtual task  read_data();
    extern virtual task  write_data();
    extern virtual task  check_status();
    extern virtual task  send_bit(bit data_bit);
    extern virtual task  clock_stretch(int delay);
    // extern virtual task  polling();                                          // TODO
    
endclass // i2c_slave_driver

//-------------------------------------------------------------------------------------------------------------
function i2c_slave_driver:: new(string name, uvm_component parent);
    super.new(name, parent);
endfunction // i2c_slave_driver::new

//-------------------------------------------------------------------------------------------------------------
function void i2c_slave_driver:: build_phase(uvm_phase phase);
    super.build_phase(phase); 
    `uvm_info("build_phase","BUILD i2c_slave_DRIVER",UVM_HIGH);
    if(!uvm_config_db#(virtual i2c_if)::get(this, "", "i2c_vif", i2c_vif)) 
        `uvm_fatal("build_phase",{"virtual interface must be set for: ", get_full_name(),".i2c_vif"});
    if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg)) begin
        `uvm_fatal("build_phase", "cfg wasn't set through config db");
    end
endfunction // i2c_slave_driver::build_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_slave_driver:: run_phase(uvm_phase phase);
  do_init();
	@(posedge i2c_vif.reset_n);
	repeat(3) @(posedge i2c_vif.system_clock);
	
  forever begin 
    
    fork
      detect_start_cond();
      detect_stopt_cond();
      // do_drive();
    join_any
    disable fork;

    // Unexpected condition logging
    rsp.transfer_failed = 'b1;
    rsp.set_id_info(req);                                                         // TODO response needed?
    seq_item_port.put(rsp);

    // release lines
    i2c_vif.uvc_sda = 'bz;
    i2c_vif.uvc_scl = 'bz;
  end   // of forever
endtask// i2c_slave_driver::run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_slave_driver:: do_init();
  i2c_vif.uvc_sda = 'bz;
  i2c_vif.uvc_scl = 'bz;

  enable = 'b0;
  @(posedge i2c_vif.system_clock);  
  `uvm_info("Driver", "do_init task executed", UVM_LOW)
endtask

task i2c_slave_driver:: do_drive();
  while (enable) begin
    seq_item_port.get(req);
    rsp = i2c_item::type_id::create("rsp");

    case (req.transaction_type)
      WRITE: write_data();
      READ:  read_data();
    endcase
    
    transfer_done = 'b1;

    // release lines after each transfer
    i2c_vif.uvc_sda = 'bz;
    i2c_vif.uvc_scl = 'bz;

    `uvm_info("Driver", "do_drive task executed", UVM_LOW)
  end
endtask

task i2c_slave_driver:: detect_start_cond();
  forever begin
    `uvm_info("Driver", "checking for Start Condition", UVM_DEBUG)
    @(negedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    `uvm_info("Driver", "detected Start Condition", UVM_HIGH)
    disable do_drive;

    // else if ... (not init Start Condition)
    if (enable) begin

      // check if EARLY Start Condition
      if (!transfer_done) begin
        `uvm_warning("Driver", "Early Start Condition")
        break;
      end

      // TODO get new speed mode
      // ! not needed below (if enable, dont forget the delay below)
    end
    // else ... (is init Start Condition)

    // wait for Master to finish Start Cond
    #10;

    counter_reset = 'b1;
    enable = 'b1;
    fork
      do_drive();
    join_none
  end
endtask

task i2c_slave_driver:: detect_stopt_cond();
  forever begin
    `uvm_info("Driver", "checking for stop condition", UVM_DEBUG)
    @(posedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    `uvm_info("Driver", "Detected Stop Condition", UVM_HIGH)
    disable do_drive;

    enable = 'b0;

    if (!transfer_done) begin
      `uvm_warning("Driver", "Early Stop Condition")
      break;
    end

  end
endtask

task i2c_slave_driver:: read_data();
  
  for (bit_index = 7; bit_index >= 0; bit_index--) begin
    // if (reset_counter) begin
    //   bit_index = 7;
    //   reset_counter = 'b0;
    // end
    // check_status();
    fork
      if (!transfer_done) clock_stretch(req.clock_stretch_data[bit_index]);
      @(posedge i2c_vif.scl);  // block until posedge clock
    join
    rsp.data[bit_index] = i2c_vif.sda;

    if (bit_index == 0) begin
      rsp.set_id_info(req);                                                         // TODO response needed?
      seq_item_port.put(rsp);
    end

    `uvm_info("Driver", $sformatf("Got bit %1d with value %1b", bit_index, rsp.data[bit_index]), UVM_DEBUG)

    // wait for end of pulse
    @(negedge i2c_vif.scl);
    //! Fcn skip first bit if condition
    // transfer_done flag reset after first bit in case of (repeated) start condition
    transfer_done = 'b0;
    #5;                                                                         // TODO (5*twentyth)
  end
  
  fork
    send_bit(req.ack_nack);
    clock_stretch(req.clock_stretch_ack);
    @(posedge i2c_vif.scl);
  join

  @(negedge i2c_vif.scl);
  #5;
endtask

task i2c_slave_driver:: write_data();

  for (bit_index = 7; bit_index >= 0; bit_index--) begin
    // if (reset_counter) begin
    //   bit_index = 7;
    //   reset_counter = 'b0;
    // end
    // check_status();
    fork
      send_bit(req.data[bit_index]);
      if (!transfer_done) clock_stretch(req.clock_stretch_data[bit_index]);
      @(posedge i2c_vif.scl);
    join

    @(negedge i2c_vif.scl);
    // transfer_done flag reset after first bit in case of (repeated) start condition
    transfer_done = 'b0;
    #5;
  end

  // release SDA for Master to ACK/NACK
  wait(i2c_vif.scl == 'b0);
  i2c_vif.uvc_sda = 'bz;
  `uvm_info("Driver", "Released SDA for ACK", UVM_HIGH)

  @(posedge i2c_vif.scl);

  rsp.ack_nack = i2c_vif.sda;
  rsp.set_id_info(req);                                                         // TODO response needed?
  seq_item_port.put(rsp);

  @(negedge i2c_vif.scl);
  #5;
endtask

task i2c_slave_driver:: check_status();
  if (!enable) wait (enable);
  if (counter_reset) begin
    bit_index = 7;
    counter_reset = 'b0;
  end
endtask

task i2c_slave_driver:: send_bit(bit data_bit);
  wait(i2c_vif.scl == 'b0);
  if (data_bit == 1) i2c_vif.uvc_sda = 'bz;
  else               i2c_vif.uvc_sda = data_bit;
  if (data_bit == 1) `uvm_info("Driver", "SDA was driven with Z", UVM_DEBUG)
  else               `uvm_info("Driver", "SDA was driven with 0", UVM_DEBUG)
endtask

task i2c_slave_driver:: clock_stretch(int delay);
  if (delay == 0) return;

  // else ...
  i2c_vif.uvc_scl = 'b0;
  #(delay);
  i2c_vif.uvc_scl = 'bz;
endtask