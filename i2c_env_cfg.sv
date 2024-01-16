/*
 * * * Environment configuration class. By default it just defines that env will have 2 agents, and creates two agent configurations. * * *
      One agent will be Master, other will be Slave.
      Add or remove fields and constraints to meet your specific needs.
 */
class i2c_env_cfg extends uvm_object;
  `uvm_object_utils(i2c_env_cfg)     
  
  i2c_cfg slave_config;
  i2c_cfg master_config;    
  int connect_master_to_sb;
  int connect_slave_to_sb;
  
  extern function new(string name = "i2c_env_cfg");
endclass

function i2c_env_cfg:: new(string name = "i2c_env_cfg");
  super.new(name);
  master_config = i2c_cfg::type_id::create ("master_config");
  slave_config = i2c_cfg::type_id::create ("slave_config");
endfunction
