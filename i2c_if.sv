
interface i2c_if (input bit system_clock, input bit reset_n);
    
  // * * * Add you specific interface logics below * * *
  logic uvc_sda;
  logic uvc_scl;

  tri1 sda;
  tri1 scl;

  assign sda = uvc_sda;
  assign scl = uvc_scl;
  
  modport dut (
  inout sda, scl
  );

  modport uvc (
  input sda, scl,
  output uvc_sda, uvc_scl
  );
  
//   always @(sda === 1'bz) begin
//     sda = 1;
//   end
  
//   always @(scl === 1'bz) begin
//     scl = 1;
//   end

  task wait_n_clocks(int N);
    // * * * This task is just a blocking function that waits N clock cycles. * * *
    repeat(N) @(posedge system_clock);
    #10;
  endtask

  // * * * You can add assertion checkers bellow * * * 
  always @(sda) assert (sda !== 1'bx);
  always @(scl) assert (scl !== 1'bx);

  always @(uvc_sda) begin
    assert (uvc_sda !== 1'bx);
    assert (uvc_sda !== 1'b1);
  end

  always @(uvc_scl) begin
    assert (uvc_scl !== 1'bx);
    assert (uvc_sda !== 1'b1);
  end

endinterface   
    


