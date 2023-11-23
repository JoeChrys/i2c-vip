
interface i2c_if (input bit system_clock, input bit reset_n);
    
  // * * * Add you specific interface logics below * * *
  logic uvc_sda;
  logic uvc_scl;

  wire sda;
  wire scl;
  
  modport dut (
    inout sda, scl
  );

  modport uvc (
    input sda, scl,
    output uvc_sda, uvc_scl
  );

  // Counter for clock pulses
  integer counter = 0;

  // Reset the counter at START or STOP condition
  always @(negedge sda or posedge sda) begin
    if (scl)  // Check if SCL is high
      counter = 0;
  end

  // Increment the counter at every positive edge of SCL
  always @(posedge scl) begin
    counter = counter + 1;
  end

  task wait_n_clocks(int N);
    // * * * This task is just a blocking function that waits N clock cycles. * * *
    repeat(N) @(posedge system_clock);
    #10;
  endtask

  // * * * You can add assertion checkers bellow * * * 
  // Property for stable SDA when SCL is high
  property p_sda_stable;
    @(posedge scl) disable iff (!scl) (!($rose(sda) || $fell(sda)) && (counter % 9 != 0));
  endproperty

  // Assertion for stable SDA when SCL is high
  a_sda_stable: assert property (p_sda_stable)
  else $error("SDA changed while SCL was high");

  // Property for START or STOP condition after 9*N clock pulses
  property p_start_stop_condition;
    @(posedge scl) disable iff (!scl) (($rose(sda) || $fell(sda)) -> (counter % 9 == 0));
  endproperty

  // Assertion for START or STOP condition after 9*N clock pulses
  a_start_stop_condition: assert property (p_start_stop_condition)
  else $error("START or STOP condition not after 9*N clock pulses");

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


// ! May need to move the following assertions into each agent/driver
// ! depending if it's a master or slave
  // expect following assertion to fail when multiple masters are driving
  always @(uvc_sda === 'bz) assert (sda == 'b1);

  // expect following assertion to fail when slave is clock stretching
  always @(uvc_scl === 'bz) assert (scl == 'b1);

endinterface