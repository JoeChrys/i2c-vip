## Notes and Ideas

#### Environment

- `env_cfg` `has_master_agent_1` ???
#### Master Driver

- RSP just read from `SDA`, sequence will compare if it is correct
<br>

- Got NACK from slave ? Then skip sequence and address another slave!
<br>

- ~~Start Condition Task~~
    - Aproach 1: 
        1. `SDA = 0`
        2. `wait(SDA == 0)`
        3. `SCL = 0`
    - Aproach 2: 
        1. `SDA = 0`
        2. `#0`
        3. `SCL = 0`
    - Approach 3:
        1. `SDA = 0`
        2. `SCL <= 0`
<br>

- At `ACK` stage
    1. Drive `SCL = 'b0` during the last part of final bit as expected
    2. Drive `SCL = 'bZ` (at this point Slave may hold `SCL = 'b0`)
    3. `wait (SCL == 'b1)`
    4. check `ACK`
    5. ...
#### Slave Driver

- Got NACK from master ? Then stop sending (skip the next WRITE packets)
<br>

-  Listen Task
    1. Check `Start Condition`
    2. `fork`
        - Listen Task (__risky?__) (detects `Start Condition`)
        - Listen for valid address and answer accordingly
        - Check `Stop Condition`
    3. `join_any`
    4. `disable join`

    

#### Monitor

- Sample at `SCL low`, this makes it indepentent of speed mode
    - `fork` checks for `START`, `STOP`


#### Speed Modes

- Make a class for clock timing (__will be used for `delays` and `SCL` in different speed modes__)
    - `m_enum {STD, FM, FMP, HS}`
    - `get_clock_percentile()` (maybe 20 percentiles)
    - `get_clock_period()`
    - `get_clock_duty()`



### Presentation / Thesis
- ##### Explain all communication types
    - Start Condition (S)
        - Repeated Start (Sr)
    - Stop Condition
    - Byte
        - Reserved address
        - Address WRITE
        - Address Read
        - Data

- ##### Start Condition
    - Resets address
    - __Doesn't__ reset speed mode
    - Puts slave devices to read mode (listen for address)
    - (Repeated) Does __not__ allow slave devices to edit their registers

- ##### Stop Condition
    - Resets everything
    - Makes slave devices check for Start Condition
    - Lets devices process the values in their registers