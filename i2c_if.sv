
interface i2c_if ();
    
    // * * * Add you specific interface logics below * * *
    tri1 sda;
    tri1 scl;

    logic uvc_sda;
    logic uvc_scl;

    assign sda = uvc_sda;
    assign scl = uvc_scl;

    /* OLD LOGIC
    //logic vdd = 'b1; // TODO maybe use supply1 instead of logic
    //logic sda, scl;    // TODO could also try wand/triand nets, even better a tri1 (actually tri1 is not better)

    // buf(pull1, strong0) (sda, vdd);
    // buf(pull1, strong0) (scl, vdd);
    //pullup(sda, scl);

    */

    // * * * You can add assertion checkers bellow * * * 
    

endinterface   
    


