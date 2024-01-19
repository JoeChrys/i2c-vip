
class i2c_slave_driver extends uvm_driver #(i2c_item);
  `uvm_component_utils(i2c_slave_driver)

  virtual i2c_if          i2c_vif;

  i2c_cfg                 cfg;

  bit                     enable;
  int                     bit_index;
  bit                     counter_reset;
  bit                     transfer_done;

  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase (uvm_phase phase);
  extern virtual task  run_phase (uvm_phase phase);
  extern virtual task  do_init();
  extern virtual task  do_drive();

  extern virtual task  detect_start_cond();
  extern virtual task  detect_stopt_cond();
  extern virtual task  read_data();
  extern virtual task  write_data();
  extern virtual task  send_bit(bit data_bit);
  extern virtual task  clock_stretch();
  extern virtual task  release_sda();
  extern virtual task  release_scl();
  extern virtual task  polling();
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
      case (cfg.slave_driver_type)
        PERIPHERAL_DEVICE: detect_start_cond();
        POLLING_CPU: polling();
      endcase
      detect_stopt_cond();
    join_any
    disable fork;

    // Unexpected condition logging
    rsp.transfer_failed = 'b1;
    rsp.set_id_info(req);
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
  transfer_done = 'b1;
  @(posedge i2c_vif.system_clock);
endtask


task i2c_slave_driver:: detect_start_cond();
  forever begin
    @(negedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    `uvm_info("Driver", "detected Start Condition", UVM_HIGH)

    // else if ... (Repeated Start Condition)
    if (enable) begin

      // check if EARLY Start Condition
      if (!transfer_done) begin
        `uvm_warning("Driver", "Early Start Condition")
        //? TODO get default speed mode
        break;
      end

      if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg)) begin
        `uvm_fatal("run_phase", "cfg wasn't set through config db");
      end
    end
    // else ... ([init] Start Condition)
    enable = 'b0;
    disable do_drive;
    #(cfg.get_delay());

    fork
      do_drive();
    join_none

    // wait for Master to finish Start Cond
    #(cfg.get_delay());
    enable = 'b1;
  end
endtask

task i2c_slave_driver:: detect_stopt_cond();
  forever begin
    @(posedge i2c_vif.sda);
    if (i2c_vif.scl == 'b0) continue;

    `uvm_info("Driver", "Detected Stop Condition", UVM_HIGH)
    disable do_drive;
    if (cfg.slave_driver_type == POLLING_CPU) begin
      disable detect_start_cond;
    end

    enable = 'b0;

    if (!transfer_done) begin
      `uvm_warning("Driver", "Early Stop Condition")
      break;
    end

  end
endtask

task i2c_slave_driver:: do_drive();
  wait (enable);
  while (enable) begin
    seq_item_port.peek(req);
    rsp = i2c_item::type_id::create("rsp");
    rsp.transaction_type = req.transaction_type;

    case (req.transaction_type)
      READ:  read_data();
      WRITE: write_data();
    endcase
    
    transfer_done = 'b1;
  end
endtask

task i2c_slave_driver:: read_data();
  for (bit_index = 7; bit_index >= 0; bit_index--) begin
    @(posedge i2c_vif.scl);
    rsp.data[bit_index] = i2c_vif.sda;
    @(negedge i2c_vif.scl);

    if (bit_index == 7) begin
      seq_item_port.get(req);
      transfer_done = 'b0;
    end
    if (bit_index == 0) begin
      rsp.set_id_info(req);
      seq_item_port.put(rsp);
    end
    `uvm_info("Driver", 
      $sformatf("Got bit[%1d] = %1b", 
        bit_index, rsp.data[bit_index]), 
      UVM_HIGH)

    fork
      clock_stretch();
    join_none
    #(cfg.get_delay());
  end

  send_bit(req.ack_nack);
  @(posedge i2c_vif.scl);
  @(negedge i2c_vif.scl);
  fork
    clock_stretch();
  join_none
  #(cfg.get_delay());
  release_sda();
endtask

task i2c_slave_driver:: write_data();
  for (bit_index = 7; bit_index >= 0; bit_index--) begin
    send_bit(req.data[bit_index]);
    @(posedge i2c_vif.scl);
    @(negedge i2c_vif.scl);

    if (bit_index == 7) begin
      seq_item_port.get(req);
      transfer_done = 'b0;
    end
    `uvm_info("Driver", 
      $sformatf("Sent bit[%1d] = %b", 
        bit_index, req.data[bit_index]), 
      UVM_HIGH)

    fork
      clock_stretch();
    join_none
    #(cfg.get_delay());
  end

  // release SDA for Master to ACK/NACK
  release_sda();
  `uvm_info("Driver", 
    $sformatf("Sent byte = %2h",
      req.data) 
    UVM_MEDIUM)
  @(posedge i2c_vif.scl);

  rsp.ack_nack = i2c_vif.sda;
  rsp.set_id_info(req);
  seq_item_port.put(rsp);

  @(negedge i2c_vif.scl);
  fork
    clock_stretch();
  join_none
  #(cfg.get_delay());
  if (rsp.ack_nack == `NACK) enable = 'b0;
endtask

task i2c_slave_driver:: send_bit(bit data_bit);
  if (i2c_vif.scl != 'b0) `uvm_error("Driver", "SCL unexpected HIGH")
  if (data_bit == 0) i2c_vif.uvc_sda = data_bit;
  else               i2c_vif.uvc_sda = 'bz;
endtask

task i2c_slave_driver:: release_sda();
  if (i2c_vif.scl == 'b1) `uvm_error("Driver", "SCL unexpected HIGH when releasing SDA")
  i2c_vif.uvc_sda = 'bz;
endtask

task i2c_slave_driver:: release_scl();
  if (i2c_vif.scl == 'b1) `uvm_error("Driver", "SCL unexpected HIGH, call this task only after 'clock_stretch()'")
  i2c_vif.uvc_scl = 'bz;
endtask

task i2c_slave_driver:: clock_stretch();
  int delay = 0;
  if (i2c_vif.scl == 'b1) `uvm_error("Driver", "SCL unexpected HIGH when clock stretching")
  if (bit_index < 0) delay = req.clock_stretch_ack;
  else               delay = req.clock_stretch_data[bit_index];

  if (delay == 0) return;

  // else ...
  i2c_vif.uvc_scl = 'b0;
  #(delay*cfg.get_delay(QUANTUM));
  `uvm_info("Driver",
    $sformatf("DONE Clock Stretch Data for %04d tu", 
      delay*cfg.get_delay(QUANTUM)), 
    UVM_HIGH)
endtask

task i2c_slave_driver:: polling();
  bit[7:1] temp_data;

  forever begin
    @(negedge i2c_vif.sda iff i2c_vif.scl);

    for (int i = 7; i >= 0; i--) begin
      @(posedge i2c_vif.scl);
      temp_data[i] = i2c_vif.sda;
      @(negedge i2c_vif.scl);
    end

    if (temp_data == START_BYTE) begin
      fork
        detect_start_cond();
      join
    end
  end
endtask