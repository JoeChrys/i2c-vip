
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
    output sda, scl,
    input uvc_sda, uvc_scl
  );

  // Counter for clock pulses
  integer counter = 0;
  // Reset the counter at START or STOP condition
  always @(negedge sda or posedge sda) begin
    if (scl)  // Check if SCL is high
      counter = -1;
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
endinterface