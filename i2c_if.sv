
interface i2c_if (input bit system_clock, input bit reset_n);
    
  // * * * Add you specific interface logics below * * *
  logic sda;
  logic scl;
  
  always @(sda === 1'bz) begin
    sda = 1;
  end
  
  always @(scl === 1'bz) begin
    scl = 1;
  end

  task wait_n_clocks(int N);
    // * * * This task is just a blocking function that waits N clock cycles. * * *
    repeat(N) @(posedge system_clock);
    #10;
  endtask

  // * * * You can add assertion checkers bellow * * * 
  always @(sda or scl) begin
    assert (sda !== 1'bx);
    assert (scl !== 1'bx);
  end

endinterface   
    


