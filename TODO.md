## TODO:
- [x] Verification Plan

- [x] Data item
    - [x] Member variables
    - [x] Constraints
    - [x] Register variables to factory

  - [x] Sequence
    - [x] Start - Finish - Get response item
    - [x] check data byte or ACK
    - [x] change ack_nack
    - [x] Master Reserved
    - [ ] [Optional] Master, stop if NACK/Fail
    - [x] Slave normal and reserved
    - [x] Normal Virtual Seq
    - [x] Reserved Addr Virtual Seq
    - [ ] Vseq - Avoid reserved address in normal mode
    - [ ] Sync Vseq else fatal error

- [x] Master Driver
    - [x] Bit driving (setting SDA and SCL in the correct order prefferably without using delays)
    - [x] Bit sample after sending
    - [x] Assign Z for uvc_* in do_init()
    - [x] write
    - [x] check while writing
    - [x] read
    - [x] Add self ACK for START Byte
    - [ ] Configurable delays

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
    - [ ] Configurable delays

- [ ] Testbench
    - [x] Create 2 IF for masters and 1 IF for slave
    - [x] Connect `sda` and `scl` of all interfaces
    - [ ] [Optional] Use modports

- [x] Interface
    - [x] Interconnect wire and logic on top.sv
    - [x] Immediate assertions (validity)
    - [x] Concurrent assertions
    - [x] Task assertions

-  [ ] Coverage
    - [ ] Cover that each stage has been ended with Start(R) or Stop (exclude unexpected eg device id write with stop)
    - [ ] Cover all stages and allowed transitions
    - [ ] Cover all possible address (single bins eg device id wildcards or full cover 10bit addresses)

- [ ] Scoreboard
    - [x] Normal Read-Write
    - [x] Device ID
    - [ ] Speed mode (needs NACK)
    - [x] Rest of reserved addresses
    - [ ] Add fatal if no start condition