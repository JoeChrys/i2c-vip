
class i2c_slave_driver extends uvm_driver #(i2c_item);
    
    `uvm_component_utils(i2c_slave_driver)

    virtual i2c_if          i2c_vif;

    i2c_cfg                 cfg;
    i2c_item                rsp;

    bit                     start_detected;

    bit                     enable;
    bit                     transfer_done;

    slave_driver_type_enum  slave_driver_type = PERIPHERAL_DEVICE;              // TODO make it change in build_phase via cfg

    extern function new (string name, uvm_component parent);
    extern virtual function void build_phase (uvm_phase phase);
    extern virtual task  run_phase (uvm_phase phase);
    extern virtual task  do_init ();
    extern virtual task  do_drive(i2c_item req);

    extern virtual task  detect_start_cond();
    extern virtual task  detect_stopt_cond();
    extern virtual task  read_data();
    extern virtual task  write_data();
    extern virtual task  send_bit(bit data_bit);
    extern virtual task  clock_stretch(int delay);
    // extern virtual task  polling();                                          // TODO
    
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
    rsp = i2c_item::type_id::create("rsp");
    
    fork
      detect_start_cond();
      detect_stopt_cond();
      do_drive(req);
    join_any
    disable fork;

    // release lines after each transfer
    i2c_vif.uvc_sda = 'bz;
    i2c_vif.uvc_scl = 'bz;
  end   // of forever
endtask// i2c_slave_driver::run_phase

//-------------------------------------------------------------------------------------------------------------
task i2c_slave_driver::do_init();
  i2c_vif.uvc_sda = 'bz;
  i2c_vif.uvc_scl = 'bz;

  enable = 'b0;
  @(posedge i2c_vif.system_clock);  
  `uvm_info("Driver", "do_init task executed", UVM_LOW)
endtask

task i2c_slave_driver::do_drive(i2c_item req);
  wait (enable);

  case (req.transaction_type)
    WRITE: write_data();
    READ:  read_data();
  endcase
  transfer_done = 'b1;
  
  @(negedge i2c_vif.scl);
  #5;

   `uvm_info("Driver", "do_drive task executed", UVM_LOW)
endtask

task i2c_slave_driver::detect_start_cond();
  forever begin
    `uvm_info("Driver", "checking for Start Condition", UVM_DEBUG)
    @(negedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;
    `uvm_info("Driver", "detected Start Condition", UVM_HIGH)

    // else if ... (not init Start Condition)
    if (enable) begin
      // check if EARLY Start Condition
      assert(transfer_done)
      else begin 
        `uvm_error("Driver", "Early Start Condition")
        break;
      end

      // TODO get new speed mode
      break;
    end
    // else ... (is init Start Condition)

    enable = 'b1;
  end
endtask

task i2c_slave_driver::detect_stopt_cond();
  forever begin
    `uvm_info("Driver", "checking for stop condition", UVM_DEBUG)
    @(posedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;
    `uvm_info("Driver", "detected stop condition", UVM_HIGH)

    assert (transfer_done) 
    else begin
      `uvm_fatal("Driver", "Early Stop Condition")
    end

    enable = 'b0;
    break; 
  end
endtask

task i2c_slave_driver::read_data();
  
  for (int bit_index = 7; bit_index >= 0; bit_index--) begin
    fork
      clock_stretch(req.clock_stretch_data[bit_index]);
      @(posedge i2c_vif.scl);  // block until posedge clock
    join
    rsp.data[bit_index] = i2c_vif.sda;

    // wait for end of pulse
    @(negedge i2c_vif.scl);
    // transfer_done flag reset after first bit in case of (repeated) start condition
    transfer_done = 'b0;
    #5;                                                                         // TODO (5*twentyth)
  end
  rsp.set_id_info(req);                                                         // TODO response needed?
  seq_item_port.put(rsp);
  
  fork
    send_bit(req.ack_nack);
    clock_stretch(req.clock_stretch_ack);
    @(posedge i2c_vif.scl);
  join
endtask

task i2c_slave_driver::write_data();

  for (int bit_index = 7; bit_index >= 0; bit_index--) begin
    fork
      send_bit(req.data[bit_index]);
      clock_stretch(req.clock_stretch_ack);
      @(posedge i2c_vif.scl);
    join

    @(negedge i2c_vif.scl);
    // transfer_done flag reset after first bit in case of (repeated) start condition
    transfer_done = 'b0;
    #5;
  end

  @(posedge i2c_vif.scl);
  rsp.ack_nack = i2c_vif.sda;
  rsp.set_id_info(req);                                                         // TODO response needed?
  seq_item_port.put(rsp);
endtask

task i2c_slave_driver::send_bit(bit data_bit);
  wait(i2c_vif.scl == 'b0);
  if (data_bit == 1) i2c_vif.uvc_sda = 'bz;
  else               i2c_vif.uvc_sda = data_bit;
  if (data_bit == 1) `uvm_info("Driver", "SDA was driven with Z", UVM_DEBUG)
  else               `uvm_info("Driver", "SDA was driven with 0", UVM_DEBUG)
endtask

task i2c_slave_driver::clock_stretch(int delay)
  if (delay == 0) return;

  // else ...
  i2c_vif.uvc_scl = 'b0;
  #(delay);
  i2c_vif.uvc_scl = 'bz;
endtask