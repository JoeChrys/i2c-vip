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
    - [ ] ~~Master, stop if NACK/Fail~~
    - [x] Slave normal and reserved
    - [x] Normal Virtual Seq
    - [x] Reserved Addr Virtual Seq
    - [x] Vseq - Avoid reserved address in normal mode
    - [ ] ~~Sync Vseq else fatal error~~

- [x] Master Driver
    - [x] Bit driving (setting SDA and SCL in the correct order prefferably without using delays)
    - [x] Bit sample after sending
    - [x] Assign Z for uvc_* in do_init()
    - [x] write
    - [x] check while writing
    - [x] read
    - [x] Add self ACK for START Byte
    - [x] Configurable delays
    - [x] Update configs on START/STOP

- [x] Slave Driver
    - [x] Sample (and send RSP to seq)
    - [x] Add Start Byte functionality ~~(should get from config_db at build phase)~~
    - [x] Add clock stretching at data bits
    - [x] Add clock stretching at ack
    - [x] Assign Z for uvc_* in do_init()
    - [x] Reset speed at STOP
    - [x] Keep speed at START
    - [x] Implement START Byte check
    - [ ] ~~Listen only for certain address function (keep reserved in mind)~~
    - [x] Configurable delays
    - [x] Implement slow sampling behavior (polling START BYTE)
    - [x] Update configs on START/STOP

- [x] Testbench
    - [x] Create 2 IF for masters and 1 IF for slave
    - [x] Connect `sda` and `scl` of all interfaces
    - [ ] ~~Use modports~~

- [x] Interface
    - [x] Interconnect wire and logic on top.sv
    - [x] Immediate assertions (validity)
    - [x] Concurrent assertions
    - [x] Task assertions

- [x] Coverage
    - [x] Cover that each stage has been ended with Start(R) or Stop (exclude unexpected eg device id write with stop)
    - [x] Cover all stages and allowed transitions
    - [x] Cover all possible address (single bins eg device id wildcards or full cover 10bit addresses)
    - [x] Instatiate cov in env and pass it to scoreboard

- [x] Scoreboard
    - [x] Normal Read-Write
    - [x] Device ID
    - [x] Speed mode (needs NACK)
    - [x] Rest of reserved addresses
    - [x] Add fatal if no start condition

- [ ] Tests
    - [x] Make a 2 master base test
    - [ ] Init vseq master 2

- [x] Env
    - [x] Make a multimaster env
    - [ ] ~~Make a multimaster env config~~

- [x] Cleanup
    - [x] Remove UVM_DEBUG prints
    - [x] Remove //TODO and //! comments
    - [ ] [Optional] Remove depedency on system_clock

- [ ] Virtual Sequence
    - [ ] [Optional] Reduce code by paremeterizing
    - [ ] Add remaining reserved addresses

- [ ] Scripts
    - Testlist
    - args in file