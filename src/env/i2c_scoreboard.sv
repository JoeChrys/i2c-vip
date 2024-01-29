`uvm_analysis_imp_decl(_m_mon) //master monitor
`uvm_analysis_imp_decl(_s_mon) //slave monitor

class i2c_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(i2c_scoreboard)

  i2c_cfg cfg;

  uvm_analysis_imp_m_mon #(i2c_item, i2c_scoreboard) m_mon_imp; // master monitor
  uvm_analysis_imp_s_mon #(i2c_item, i2c_scoreboard) s_mon_imp; // slave monitor
  i2c_coverage cov;
  
  i2c_item item_q[$];
  i2c_item current_item;
  int write_flag;
  int start_index;

  int expect_start;
  int expect_stop;
  int expect_ack;

  scoreboard_state_enum current_state;
  scoreboard_state_enum next_state;

  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase (uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void write_m_mon(i2c_item item);
  extern virtual function void write_s_mon(i2c_item item);
  extern virtual function void reset();
  extern virtual function void set_state(scoreboard_state_enum state);
  extern virtual function void check_start();
  extern virtual function void check_stop();
  extern virtual function void check_ack();
endclass // i2c_scoreboard

function i2c_scoreboard:: new(string name, uvm_component parent);
  super.new(name,parent);
endfunction // i2c_scoreboard::new

function void i2c_scoreboard:: build_phase(uvm_phase phase);
  super.build_phase(phase);

  m_mon_imp = new("m_mon_imp", this);
  s_mon_imp = new("s_mon_imp", this);
  if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg)) begin
    `uvm_fatal("build_phase", "cfg wasn't set through config db");
end
endfunction // i2c_scoreboard::build_phase

function void i2c_scoreboard:: write_m_mon(i2c_item item);
  `uvm_info("Scoreboard", "Just recieved item from master monitor", UVM_FULL)
endfunction // i2c_scoreboard::write_m_mon

function void i2c_scoreboard:: write_s_mon(i2c_item item);
  `uvm_info("Scoreboard", "Just recieved item from slave monitor", UVM_MEDIUM)

  item_q.push_back(item);
  write_flag = 1;
endfunction // i2c_scoreboard::write_s_mon

/*
 * The scoreboard is implemented as a state machine.
 * This task is the main task of the scoreboard. It is responsible for
 * checking the data that is received from the monitors and comparing it
 * to the expected data. It also checks the start and stop conditions.
 * Depending on the data received, it will change the state of the scoreboard.
 */
task i2c_scoreboard:: run_phase(uvm_phase phase);
  current_state = WAIT_FOR_START;
  next_state = WAIT_FOR_START;

  forever begin
    wait (write_flag);
    write_flag = 0;

    current_item = item_q[$];
    if (cfg.has_coverage) begin
      cov.i2c_end_state_with_start_stop.sample(current_item, current_state);
    end

    check_start();

    case (current_state)
    ADDRESSING: begin

      if (current_item.data == START_BYTE) begin

        `uvm_info("Scoreboard", "Start byte", UVM_LOW)
        next_state = WAIT_FOR_START;

      end
      else if (current_item.data == GENERAL_CALL) begin

        `uvm_info("Scoreboard", "General call", UVM_LOW)
        next_state = GENERAL_CALL_STATE;

      end
      else if (current_item.data[7:1] == C_BUS) begin

        `uvm_info("Scoreboard", "C-BUS Address", UVM_LOW)
        next_state = CBUS_STATE;

      end
      else if (current_item.data[7:1] == OTHER_BUSES) begin

        `uvm_info("Scoreboard", "OTHER BUSES Reserved Address", UVM_LOW)
        next_state = OTHER_BUS_STATE;

      end
      else if (current_item.data[7:1] == FUTURE_PURPOSE) begin

        `uvm_info("Scoreboard", "FUTURE PURPOSE Reserved Address", UVM_LOW)
        next_state = FUTURE_PURPOSE_STATE;

      end
      else if (current_item.data[7:3] == SPEED_MODE) begin
        
        `uvm_info("Scoreboard", "SPEED MODE Reserved Address", UVM_LOW)
        expect_ack = -1;
        cfg.toggle_speed_mode();
        next_state = WAIT_FOR_START;

      end
      else if (current_item.data[7:3] == DEVICE_ID) begin
          
        if (current_item.data[0] == `W) begin
          `uvm_info("Scoreboard", "DEVICE ID Reserved Address WRITE", UVM_LOW)
          next_state = DEVICE_ID_WRITE;
        end
        else if (current_item.data[0] == `R) begin
          `uvm_info("Scoreboard", "DEVICE ID Reserved Address READ", UVM_LOW)
          if (current_item.data[7:1] != item_q[start_index-2].data[7:1]) begin
            `uvm_warning("Scoreboard", "Device ID does not match")
          end
          next_state = DEVICE_ID_READ;
        end

      end
      else if (current_item.data[7:3] == TEN_BIT_TARGET_ADDRESSING) begin
          
          if (current_item.data[0] == `W) begin
            `uvm_info("Scoreboard", "10-BIT TARGET Reserved Address WRITE", UVM_LOW)
            next_state = TEN_BIT_ADDR_WRITE;
          end
          else if (current_item.data[0] == `R) begin
            `uvm_info("Scoreboard", "10-BIT TARGET Reserved Address READ", UVM_LOW)
            if (current_item.data[7:1] != item_q[start_index-2].data[7:1]) begin
              `uvm_error("Scoreboard", "10-bit first 7 bits do not match")
            end 
            next_state = TEN_BIT_ADDR_READ;
          end
      end

      else begin : NORMAL_ADDRESSING
        if (current_item.data[0] == `W) begin
          `uvm_info("Scoreboard", $sformatf("Target Address WRITE %7b", current_item.data[7:1]), UVM_LOW)
          next_state = NORMAL_WRITE;
        end
        else if (current_item.data[0] == `R) begin
          `uvm_info("Scoreboard", $sformatf("Target Address READ %7b", current_item.data[7:1]), UVM_LOW)
          next_state = NORMAL_READ;
        end
      end : NORMAL_ADDRESSING

      if (cfg.has_coverage) begin
        cov.i2c_addresses.sample(current_item, next_state);
      end

    end

    GENERAL_CALL_STATE: begin

      if (current_item.data[0] == 'b0) begin // Command
        `uvm_info("Scoreboard", $sformatf("General Call Command %7b", current_item.data[7:1]), UVM_LOW)
        next_state = WAIT_FOR_START;
      end
      else if (current_item.data[0] == 'b1) begin // Controller Address
        `uvm_info("Scoreboard", $sformatf("General Call Address %7b", current_item.data[7:1]), UVM_LOW)
        next_state = WAIT_FOR_START;
      end

    end

    CBUS_STATE: begin
      
      `uvm_info("Scoreboard", $sformatf("C-BUS Data %8b", current_item.data), UVM_LOW)
      next_state = CBUS_STATE;

    end

    OTHER_BUS_STATE: begin

      `uvm_info("Scoreboard", $sformatf("OTHER BUSES Data %8b", current_item.data), UVM_LOW)
      next_state = OTHER_BUS_STATE;

    end

    FUTURE_PURPOSE_STATE: begin

      `uvm_info("Scoreboard", $sformatf("FUTURE PURPOSE Data %8b", current_item.data), UVM_LOW)
      next_state = FUTURE_PURPOSE_STATE;

    end

    DEVICE_ID_WRITE: begin

      `uvm_info("Scoreboard", $sformatf("DEVICE ID Target %7b", current_item.data[7:1]), UVM_LOW)
      next_state = WAIT_FOR_START;

    end

    DEVICE_ID_READ: begin

      `uvm_info("Scoreboard", $sformatf("DEVICE ID Data %8b", current_item.data), UVM_LOW)
      next_state = DEVICE_ID_READ;

      if (item_q.size() == (start_index+1)+3) begin
        `uvm_info("Scoreboard", 
          $sformatf("Manufacturer ID %12b, \n Part Num %9b, Die Revision %3b",
          {item_q[start_index+1].data, item_q[start_index+2].data[7:4]},
          {item_q[start_index+2].data[3:0], item_q[start_index+3].data[7:3]},
          item_q[start_index+3].data[3:0]),
          UVM_LOW)
        next_state = WAIT_FOR_START;
      end

    end

    TEN_BIT_ADDR_WRITE: begin

      if (item_q.size() == (start_index+1)+1) begin
        `uvm_info("Scoreboard",
          $sformatf("10-BIT TARGET Address %10b", 
            {item_q[start_index].data[1:0], current_item.data}), 
          UVM_LOW)
      end
      else if (item_q.size() == (start_index+1)+2) begin
        `uvm_info("Scoreboard", $sformatf("(10-BIT) Register / Write Data %8b", current_item.data), UVM_LOW)
      end
      else begin
        `uvm_info("Scoreboard", $sformatf("(10-BIT) Write Data %8b", current_item.data), UVM_LOW)
      end

      next_state = TEN_BIT_ADDR_WRITE;

    end

    TEN_BIT_ADDR_READ: begin

      `uvm_info("Scoreboard", $sformatf("(10-BIT) Read Data %8b", current_item.data), UVM_LOW)
      next_state = TEN_BIT_ADDR_READ;

    end

    NORMAL_WRITE: begin

      if (item_q.size() == (start_index+1)+1) begin
        `uvm_info("Scoreboard", $sformatf("Register / Write Data %8b", current_item.data), UVM_LOW)
      end
      else begin
        `uvm_info("Scoreboard", $sformatf("Write Data %8b", current_item.data), UVM_LOW)
      end

      next_state = NORMAL_WRITE;

    end

    NORMAL_READ: begin

      `uvm_info("Scoreboard", $sformatf("Read Data %8b", current_item.data), UVM_LOW)
      next_state = NORMAL_READ;

    end

    default: begin
      `uvm_error("Scoreboard", "Invalid state")
    end
    endcase

    check_ack();
    check_stop();
    set_state(next_state);
  end
endtask // i2c_scoreboard::run_phase

/*
 * This function resets the scoreboard to its initial state.
 * Any data that was in the queue is deleted since it no longer affects
 * the current communication. It is called when a stop condition is detected.
 */
function void i2c_scoreboard:: reset();
  item_q.delete();
  expect_start = 0;
  expect_stop = 0;
  expect_ack = 0;
  start_index = -1;
endfunction // i2c_scoreboard::reset

/*
 * This function sets the state of the scoreboard.
 * It is called when a start condition is detected and when the whole transaction
 * item has been processed.
 */
function void i2c_scoreboard:: set_state(scoreboard_state_enum state);
  case (state)
    WAIT_FOR_START: begin
      expect_start = 1;
      expect_stop = 0;
      expect_ack = 0;
    end
    NORMAL_WRITE,
    ADDRESSING,
    GENERAL_CALL,
    CBUS_STATE,
    OTHER_BUS_STATE,
    FUTURE_PURPOSE_STATE,
    TEN_BIT_ADDR_WRITE: begin
      expect_start = 0;
      expect_stop = 0;
      expect_ack = 1;
    end
    NORMAL_READ,
    DEVICE_ID_READ,
    TEN_BIT_ADDR_READ: begin
      expect_start = 0;
      expect_stop = 0;
      expect_ack = 0;
    end
    default: begin
      `uvm_error("Scoreboard", "Invalid state")
    end
  endcase
  current_state = state;
endfunction // i2c_scoreboard::set_state

/*
 * This function checks if the start condition is correct.
 * It sets the start_index to the index of the start condition in the queue.
 * Immediately sets the state to ADDRESSING if start condition is detected.
 */
function void i2c_scoreboard:: check_start();
  if (expect_start == 1 && !current_item.start_condition) begin
    `uvm_error("Scoreboard", "Expected start condition")
  end
  if (expect_start == -1 && current_item.start_condition) begin
    `uvm_error("Scoreboard", "Unexpected start condition")
  end
  if (current_item.start_condition) begin
    `uvm_info("Scoreboard", "Initiating Communication", UVM_LOW)
    start_index = item_q.size()-1;
    set_state(ADDRESSING);
  end
  if (start_index < 0) begin
    `uvm_fatal("Scoreboard", "Expected start condition at the beginning")
  end
endfunction // i2c_scoreboard::check_start

/*
 * This function checks if the stop condition is correct.
 * It resets the scoreboard if stop condition is detected.
 */
function void i2c_scoreboard:: check_stop();
  if (expect_stop == 1 && !current_item.stop_condition) begin
    `uvm_error("Scoreboard", "Expected stop condition")
  end
  if (expect_stop == -1 && current_item.stop_condition) begin
    `uvm_error("Scoreboard", "Unexpected stop condition")
  end
  if (current_item.stop_condition) begin
    `uvm_info("Scoreboard", "BUS is IDLE\n", UVM_LOW)
    reset();
    cfg.reset_speed_mode();
    next_state = WAIT_FOR_START;
  end
endfunction // i2c_scoreboard::check_stop

/*
 * This function checks if the ack/nack is correct.
 */
function void i2c_scoreboard:: check_ack();
  if (expect_ack == 1 && current_item.ack_nack == `NACK) begin
    `uvm_error("Scoreboard", "Expected ack")
  end
  if (expect_ack == -1 && current_item.ack_nack == `ACK) begin
    `uvm_error("Scoreboard", "Unexpected ack")
  end
endfunction // i2c_scoreboard::check_ack
