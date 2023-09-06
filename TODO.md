## Questions

##### General

- [x] 1. Should I make a modifiable clock for different speed modes?

- [ ] 2. To test `Start Byte` may need a different slave since this slave does NOT listen for `Start Condition` but for `SDA = 'b0`

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

- [ ] 1. How to drive SDA and SCL in correct order?
    - Should I use<br> ``wait(scl == 0); sda = data;`` ?

- [ ] 2. How should it work in general?
    - Wait for START - Send RSP to seqr - Drive REQ? (Normal Behavior)
    - Do random slave behavior (Write....) ..oh.. I see, just respect the protocol, listen and RSP, it depends on the sequence whether the answer will be correct

##### UVM
- [x] 1. When trying to test multiple contollers (masters), I should use a different env with 2 master agents?

### Features

##### Ultra Fast Mode

- [ ] Should I implement it according to the following spec? It is __not__ widely used. [UFM](https://www.i2c-bus.org/ultra-fast-mode-ufm/)

---

## TODO:
- [ ] Verification Plan
    - [ ] Normal behavior
        - [ ] Start - Address1|Write - Data 1.. - Start - Address2|Write - Data 1.. - Stop
        - [ ] Start - Address1|Read  - Data 1.. - Start - Address2|Read  - Data 1.. - Stop
        - [ ] Start - Address1|Write - Data 1.. - Start - Address1|Read  - Data 1.. - Stop
- [ ] Interface
    - [x] Pullup behavior when `1'bZ`
    - [x] Basic assertions for `1'bX`
    - [ ] Assertion for pullup behavior
    - [x] Assert uvc logic never `1'b1`
- [ ] Data item
    - [x] Member variables
    - [x] Constraints
    - [ ] Register variables to factory
- [ ] Driver
    - [x] Bit driving (setting SDA and SCL in the correct order prefferably without using delays)
    - [ ] Bit sample after sending
- [ ] Testbench
    - [ ] Create 2 IF for masters and 1 IF for slave
    - [ ] connect `sda` and `scl` of all interfaces

