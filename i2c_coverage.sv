/*
      * * * Coverage class, fill your specific coverpoints down bellow * * *
*/

/*    * * * UNCOMMENT AND WRITE COVERAGE BELOW * * *

class i2c_coverage extends uvm_component;
	`uvm_component_param_utils(i2c_coverage)
	
    i2c_cfg cfg; 
    
    covergroup i2c_cg with function sample(
        i2c_item item
        );
        
        // * * * * WRITE YOUR COVERPOINTS HERE * * * * 
        
    endgroup
	
    extern function new(string name = "i2c_coverage", uvm_component parent);
    extern virtual function void build_phase(uvm_phase phase);
endclass

function i2c_coverage::new(string name = "i2c_coverage", uvm_component parent);
    super.new(name, parent);
    i2c_cg = new();	
endfunction // i2c_coverage::new

function void  i2c_coverage::build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(i2c_cfg)::get(this, "", "cfg", cfg))   
        `uvm_fatal("build_phase", "cfg wasn't set through config db");
endfunction // i2c_coverage::build_phase

*/
