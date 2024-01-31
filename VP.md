# Verification Plan

#### Notes
- Data after START is always an Address.
- Data after address is [usually] the register pointer.
- Data (W) means WRITE for the Master and Read for the slave unless specified otherwise.
- Similarly, Data (R) means READ for the Master and Write for the slave.

## Single Master

##### Functionality
1. __Test UVC reseting__ `[Start - Data* (W) - Stop]*`
    __Send one byte, with Start and Stop, multiple times__
    - Random Data Bytes[1:2], Byte[0] = Address, [Byte[1] = Register]
1. __Test Repeated Start functionality__ `[Start - Data[2] (W)]* - Stop`
    __Send multiple Start and addresses, send Stop only at the end__
    - Address certain device and register, reset, repeat
<!--
1. __Test read from standby bus__ `Start - Data (R) - Stop`
    __Read without addressing a target device__
    - Special 'error' case, it is not detectable on the interface
    - Data will be `'hFF` which is a reserved address for Device ID
    - Note: can be avoided with a hard constraint
1. __Test Read without selecting register__ `Start - Data (W) - Data* (R) - Stop`
    __Adress target to read directly, read bytes sent__
    - Not used but technically it should work and does not violate the protocol
    - Should expect unexpected behavior from a DUT or in a real application
-->

### Basic
##### Write
1. __Test basic Write functionality__ `Start - Data[2] (W) - Data* (W) - Stop`
    __Send 2 bytes (for addressing) and a random amound of data bytes, with Start and Stop__
    - (Default) Address certain device and register and Write (avoid reserved address)
1. __Test Repeated Start functionality with Data__ `[Start - Data[2] (W) - Data* (W)]* - Stop`
    __Send multiple Start, addresses and random data, send Stop only at the end__
    - Address certain device and register, write, reset, repeat

##### Read
1. __Test basic Read functionality__ `Start - Data[2] (W) - Start - Data (W) - Data* (R) - Stop`
    __Address target, switch to Reading Mode, read random data__
    - (Default) Address certain device and register, address device again to read, read bytes
    - The functionality before `Data* (R)` has been verified in __Write__
1. __Test Repeated Start functionality with Data__ `[Start - Data[2] (W) - Start - Data (W) - Data* (R)]* - Stop`
    __Send START, Address target, switch to Reading Mode, read random data, repeat__
    - Address certain device and register, write, reset, repeat

##### Reserved Addresses
1. __Test Start Byte__ `Start - 'b0000_0001 - Start - Data* - Stop`
  __Send Start Byte and continue communication normally__
    - Target should be on slow polling to test

1. __Test High Speed Mode Adresses__ `Start - 'b0000_1xxx - Start - Data* - Stop`
    __Send High Speed Address and continue communication normally__
    - New speed on Start (keep on repeated Start)
    - Reset speed on Stop
    - No ACK required

###### Unnecessary RA Tests (will be skipped)
1. __Test General Call Command__ `Start - 'b0000_0000 - 'bxxxx_xxx0 - Stop`
  __Send General Call Adreess followed by the General Call Command__

1. __Test Controller Address__ `Start - 'b0000_0000 - 'bxxxx_xxx1 - Stop`
  __Send General Call Adreess followed by controller (master) address__

1. __Test Other Bus Adresses__
    - __CBUS__ `Start - 'b0000_001x - [IGNORE] - Stop`
    __Send C-Bus reserved Adresss, Ignore (C-BUS) until Stop__
    - __Different bus format__ `Start - 'b0000_010x - [IGNORE] - Stop`
    __Send Different bus format reserved Adresss, Ignore until Stop__
    - __[Future Purpose]__ `Start - 'b0000_011x - [IGNORE] - Stop`
    __Send [Future Purpose] reserved Adresss, Ignore until Stop__

1. __Test Device ID Address__ `Start - 'b1111_1xx0 - Addr - Start - 'b1111_1xx1 - Data[3] (R) - Stop`
  __Send Device ID address, then target address, switch to reading mode, read 3 bytes__
    - Target address follows Device ID Address, LSB: x (Don't care)

1. __Test 10-bit Addressing Write__ `Start - 'b1111_0xxx - Addr (W) - Data* - Stop`
    __Send 10-bit address, then target address, write random bytes__

1. __Test 10-bit Addressing Read__ `Start - 'b1111_0xxx - Data (addr) -  Start - Addr (R) - Data* (R) - Stop`
    __Send Device ID address, then target address, switch to reading mode (only 10-bit address, no target address), read bytes__
    - No target address after repeated Start

### Extended
<!--
1. Base with __NACKS__
-->
1. Base with __Master delay__
1. Base with __Slave clock stretching at ACK__
1. Base with __Slave clock stretching Data__ and __at ACK__
1. Base with __Master delay__ and __Slave clock stretching at ACK__

### Error detection

1. __Test Master Slave concurrent Write__ `Start - Data[2] - [M:Data(W), S:Data(W)]`
    __After addressing targer, both master and slave write byte__
    - Cannot be detected on if, Driver should produce error if Data in not the same
    - None should `ACK`
1. __Test NO Start Condition__ `Data* (W) - Stop*`
    __Write bytes without Start__
    - Slave will not be enabled without Start
    - SB should produce error without Start
1. __Test Write overflow__ `Start - Data* (W) - NO_STOP - Data* (W)`
    __Write more bytes than the slave is able to read__
    - Does not violate protocol but is unwanted communication
    - Slave should not `ACK`

## Multi Master

### Base

1. Same with __Single Driver Base__
    - Masters should arbitrate data to get control of the bus

### Extended

1. Base with __Master delay__
    - No clock arbitration, the Master with the smaller delay takes control
1. Base with __Master delay__ and __Slave clock stretching at ACK__
    - Should expect the same behavior as above
1. Base with __Slave clock stretching Data__ and __at ACK__
    - Should expect the same behavior as base, Master will still use arbitration to get control