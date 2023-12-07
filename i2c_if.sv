interface i2c_if (input bit system_clock, input bit reset_n);
  // `include "uvm_macros.svh"
  // import uvm_pkg::*;
    
  // * * * Add you specific interface logics below * * *
  logic uvc_sda;
  logic uvc_scl;

  wire sda;
  wire scl;
  
  modport dut (
    inout sda, scl
  );

  modport uvc (
    output sda, scl,
    input uvc_sda, uvc_scl
  );

  initial begin
    uvc_sda = 'bz;
    uvc_scl = 'bz;
  end

  // Counter for clock pulses
  int counter;
  int full_counter;

  always @(posedge reset_n) begin
    counter <= 0;
    full_counter <= 0;
  end

  // Set the counters at START condition
  always @(negedge sda iff scl) begin
    counter <= counter - 1;
    full_counter <= full_counter - 1;
  end

  // Reset the counter at STOP condition
  always @(posedge sda iff scl) begin
    counter <= 0;
  end

  // Increment the counter at every positive edge of SCL
  always @(posedge scl) begin
    counter <= counter + 1;
    full_counter <= full_counter + 1;
  end

  task wait_n_clocks(int N);
    // * * * This task is just a blocking function that waits N clock cycles. * * *
    repeat(N) @(posedge system_clock);
    #10;
  endtask

  // * * * You can add assertion checkers bellow * * * 

  // *** Immediate Assertions for valid driver signals ***
  always @(uvc_sda) begin
    assert (uvc_sda !== 1'bx);
    // ! may need to remove if we actively drive on higher speeds
    assert (uvc_sda !== 1'b1);
  end

  always @(uvc_scl) begin
    assert (uvc_scl !== 1'bx);
    // ! may need to remove if we actively drive on higher speeds
    assert (uvc_sda !== 1'b1);
  end

  // *** Immediate Assertions for valid bus signals ***
  always @(sda) assert (sda!==1'bx);
  always @(scl) assert (scl!==1'bx);


  // *** Protocol Assertions ***
  
  // Approach 1
  // ! How to monitor the spawned threads?
  task automatic protocol_checker();
    automatic int clock_counter =  -1;
    automatic bit fail = 1;
    @(negedge scl);
    fork
      begin
        forever begin 
          @(posedge scl) clock_counter++;
        end
      end
      begin// start/stop
        @(sda iff scl);
      end
    join_any
    disable fork;
    if (clock_counter % 9 == 0) fail = 0;
    if (fail) $error("protocol_checker(): Protocol check FAILED");
  endtask
  always @(negedge sda iff scl) fork protocol_checker(); join_none

  

  // Approach 2 (uses counter)
  property p_start;
    @(negedge sda iff scl) disable iff (!reset_n) ((full_counter) % 9 == 0); // || full_counter == -1
  endproperty
  assert property (p_start);

  property p_stop;
    @(posedge sda iff scl) disable iff (!reset_n) (full_counter % 9 == 0);
  endproperty
  assert property (p_stop);

  // *** Protocol checker ***
  // When SCL is HIGH, check if START/STOP happenned in valid context
  // Also checks if SDA is stable while SCL is HIGH
  task automatic sda_stable_checker();
    automatic bit temp;
    automatic bit fail = 1;
    // could use a static local counter to make it independent of external counters

    temp = sda;
    fork
      begin : CONDITION
        @(sda) if (full_counter%9==0) fail = 0; // iff scl [optional, since other thread finishes first]
      end
      begin
        @(negedge scl) if (sda == temp) fail = 0;
      end
    join_any
    disable fork;
    if (fail) $error("sda_stable_checker(): Protocol check FAILED");
    // assert (!fail);
  endtask
  always @(posedge scl) sda_stable_checker();
  // ***

  // Approach 3 (uses counter)
  property p_i2c_check;
    @(sda iff scl) disable iff (!reset_n) (full_counter%9 == 0); // ||(counter==-1)
  endproperty
  assert property (p_i2c_check);

  property p_mc_stable_sda;
    @(negedge sda iff scl) disable iff (!reset_n) 1 ##1 @(sda iff scl) 1 |-> full_counter%9==0;
  endproperty
  assert property (p_mc_stable_sda);
endinterface