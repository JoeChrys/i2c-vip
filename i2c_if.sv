
interface i2c_if (inout sda, scl);
    
    // * * * Add you specific interface logics below * * *
    logic vdd = 'b1;

    buf(pull1, strong0) (sda, vdd);
    buf(pull1, strong0) (scl, vdd);
    
	
    // * * * You can add assertion checkers bellow * * * 
    

endinterface   
    


