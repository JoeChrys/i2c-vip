
interface i2c_if ();
    
  // * * * Add you specific interface logics below * * *
  logic sda;
  logic scl;
  
  always @(sda === 1'bz) begin
    sda = 1;
  end
  
  always @(scl === 1'bz) begin
    scl = 1;
  end

  // * * * You can add assertion checkers bellow * * * 
  always @(sda or scl) begin
    assert (sda !== 1'bx);
    assert (scl !== 1'bx);
  end

endinterface   
    


