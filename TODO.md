## TODO:
- [x] Verification Plan
    - [x] Normal behavior
        - [x] Start - Address1|Write - Data 1.. - Start - Address2|Write - Data 1.. - Stop
        - [x] Start - Address1|Read  - Data 1.. - Start - Address2|Read  - Data 1.. - Stop
        - [x] Start - Address1|Write - Data 1.. - Start - Address1|Read  - Data 1.. - Stop
        - [x] ...

- [x] Interface
    - [x] Pullup behavior when `1'bZ`
    - [x] Basic assertions for `1'bX`
    - [x] Assertion for pullup behavior
    - [x] Assert uvc logic never `1'b1`

- [x] Data item
    - [x] Member variables
    - [x] Constraints
    - [x] Register variables to factory

  - [x] Sequence
    - [x] Start - Finish - Get response item
    - [x] check data byte or ACK
    - [x] change ack_nack
    - [ ] Master Reserved
    - [ ] [Optional] Master, stop if NACK/Fail
    - [ ] Slave normal and reserved
    - [ ] Env Virtual Seq

- [x] Master Driver
    - [x] Bit driving (setting SDA and SCL in the correct order prefferably without using delays)
    - [x] Bit sample after sending
    - [x] Assign Z for uvc_* in do_init()
    - [x] write
    - [x] check while writing
    - [x] read
    - [ ] Add self ACK for START Byte

- [x] Slave Driver
    - [x] Sample (and send RSP to seq)
    - [x] Add Start Byte functionality ~~(should get from config_db at build phase)~~
    - [x] Add clock stretching at data bits
    - [x] Add clock stretching at ack
    - [x] Assign Z for uvc_* in do_init()
    - [ ] Reset speed at STOP
    - [ ] Keep speed at START
    - [ ] Implement START Byte check
    - [ ] ~~Listen only for certain address function (keep reserved in mind)~~

- [ ] Testbench
    - [ ] Create 2 IF for masters and 1 IF for slave
    - [x] Connect `sda` and `scl` of all interfaces
    - [ ] Use modports

- [ ] Interface
    - [ ] Implement assertions
    - [ ] ...

-  [ ] Coverage
    - [ ] ...

- [ ] Scoreboard
    - [ ] ...
