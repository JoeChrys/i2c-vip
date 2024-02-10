

## Questions

#### Xcelium
- [ ] How to enable assertions for every pass, not just for the first.
- [ ] How to continue the simulation even if assertion fails
- [ ] In `/tools/cdnc/xcelium` what is each folder? UVM versions?
- [x] Detailed xcelium documentation?
- [ ] Βιβλιογραφία το xcelium manual?

## Presentation / Thesis

- Ενότητα για τη χρήση του I2C

- ##### Explain all communication types
    - Start Condition (S)
        - Repeated Start (Sr)
    - Stop Condition (P)
    - Byte
        - Reserved address
        - Address WRITE
        - Address Read
        - Data

- ##### Start Condition
    - Resets address __KINDA__ (exceptions 10-bit, Device ID)
    - Puts slave devices to read mode (listen for address)
    - (Repeated) Does __not__ allow slave devices to edit their registers
    - (Repeated) __Doesn't__ reset speed mode
    - (Repeated) __Doesn't__ allow other drivers to take control

- ##### Stop Condition
    - Resets everything
    - Makes slave devices check for Start Condition
    - Lets devices process the values in their registers

---

#### Possible improvements

  - auto STOP condition process after delay (disabled when `do_drive()` is called)

---

#### Glossary
- UVM
- UVC
- VIP
- S (start)
- Sr (repeated)
- P (stop)
- W (write)
- R (read)

<!--
## Notes and Ideas

#### Environment

- ~~`env_cfg` `has_master_agent_1` ???~~
#### Master Driver

- Add self ACK for start byte?
<br>

- ~~RSP just read from `SDA`, sequence will compare if it is correct~~
<br>

- ~~Got NACK from slave ? Then skip sequence and address another slave!~~
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

- ~~At `ACK` stage~~
    1. Drive `SCL = 'b0` during the last part of final bit as expected
    2. Drive `SCL = 'bZ` (at this point Slave may hold `SCL = 'b0`)
    3. `wait (SCL == 'b1)`
    4. check `ACK`
    5. ...
#### Slave Driver

- ~~Got NACK from master ? Then stop sending (skip the next WRITE packets)~~
<br>

-  ~~Listen Task~~ __Done really differently__
    1. Check `Start Condition`
    2. `fork`
        - Listen Task (__risky?__) (detects `Start Condition`)
        - Listen for valid address and answer accordingly
        - Check `Stop Condition`
    3. `join_any`
    4. `disable join`

    
- Polling
    ```
    forever
      #delay [1:7] clocks
      if (sda = HIGH) continue;

      fork
        check_start();
        forever
          #delay 10 clocks 
          if (!enable) 
            disable check_start; // or disble fork
            break(?)
        end forever
      join_any
    end foverever
    ```
    
  - add listen_only_address field, that checks rsp.data -> toggles enable and continue

#### Monitor

- Sample at `SCL low`, this makes it indepentent of speed mode
    - `fork` checks for `START`, `STOP`


#### Speed Modes

- Make a class for clock timing (__will be used for `delays` and `SCL` in different speed modes__)
    - `m_enum {STD, FM, FMP, HS}`
    - `get_clock_percentile()` (maybe 20 percentiles)
    - `get_clock_period()`
    - `get_clock_duty()`


- ##### Assertions
(int counter = -1, counter % 9)
  - ##### Approach 1
    - Start Condition bit counter
      1. @(negedge SDA) if SCL==1 task assert;
      2. fork
          forever @(posedge clk) counter++
          begin
            fork : conditions
              forever begin
                @(negedge SDA) if (SCL) break;
              end
              forever begin
                @(posedge SDA) if (SCL) break;
              end
            join_any
          end
        join_any
        disable fork;
        if (counter % 9 == 0) pass
        else fail
      assert (pass/fail)
      endtask

- ##### Approach 2
    - property START
        @(negedge SDA) scl |-> counter % 9 == 0;
    - @(posedge scl) task sda_stable
        temp = sda;
        @(negedge scl);
        if (temp == sda || counter % 9 == 0) pass
        else fail
      endtask

- ##### Approach 3
    - property
        @(scl) disable iff (!scl) !($stable(sda)) |-> (counter % 9 == 0)


- ##### Interface
  use modports to ensume correct writing direction

  ---



##### General

- [x] 1. Should I make a modifiable clock for different speed modes?

- [x] 2. To test `Start Byte` may need a different slave since this slave does NOT listen for `Start Condition` but for `SDA = 'b0`

- [x] 3. If 2 masters are trying to send at the same time (clock sync) then the one that drives `SDA = 0` should win. Both drive it at the same time with `Z` &rarr; `1` and `0` which may lead to `X` in simulation. Should `X` be turned to `0` just like `Z` &rarr; `1` ?
May need to use nets in interface !!! (e.g. when clock strecting which assignment should win `'bZ` (from master) or `'b0` (from slave))
__A: use seperate interface for each driver, each interface has 2 logic and 2 tri1, connect all tri1 wires of all interfaces__

##### Data Item

- [x] 1. How to create a new global type (enum) for item type?

##### Master Driver

- [x] 1. How will the driver generate clock? See: [Start Condition](https://www.i2c-bus.org/repeated-start-condition/) __(would be easier to tell the difference between data and START/STOP)__
    - Should I base it on system_clock signal?
    - Clock period should be ``LOW-HIGH-LOW`` instead of ``HIGH-LOW``

        | value | time |
        |---|---|
        | LOW | ${(1-duty) \over 2} \cdot period$ |
        | HIGH | $duty \cdot period$ |
        | LOW | ${(1-duty) \over 2} \cdot period$ |

##### Slave Driver

- [x] 1. How to drive SDA and SCL in correct order?
    - Should I use<br> ``wait(scl == 0); sda = data;`` ?
    - ADD optional delay for visual purposes

- [x] 2. How should it work in general?
    - Wait for START - Send RSP to seqr - Drive REQ? (Normal Behavior)
    - Do random slave behavior (Write....) ..oh.. I see, just respect the protocol, listen and RSP, it depends on the sequence whether the answer will be correct

##### UVM
- [x] 1. When trying to test multiple contollers (masters), I should use a different env with 2 master agents?

#### Features
- ##### Ultra Fast Mode
    - [x] Should I implement it according to the following spec? It is __not__ widely used. [UFM](https://www.i2c-bus.org/ultra-fast-mode-ufm/) 
    Better no!?
-->

