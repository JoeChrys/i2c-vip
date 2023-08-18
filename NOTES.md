## Notes and Ideas

#### Master Driver

- Com Task
    1. Check if bus is free
    2. `fork` 
        - `Start COM` 
        - Check `Start Condition`
    - No other driver can `Stop Condition`
    3. `join_any`
    4.  `disable fork`
<br>

- Start Condition Task
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

#### Slave Driver

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

#### Clocking

- At `ACK` stage
    1. Drive `SCL = 'b0` during the last part of final bit as expected
    2. Drive `SCL = 'bZ` (at this point Slave may hold `SCL = 'b0`)
    3. `wait (SCL == 'b1)`
    4. check `ACK`
    5. ...

#### Speed Modes

- Make a class for clock timing (__will be used for `delays` and `SCL` in different speed modes__)
    - `m_enum {STD, FM, FMP, HS}`
    - `get_clock_percentile()` (maybe 20 percentiles)
    - `get_clock_period()`
    - `get_clock_duty()`