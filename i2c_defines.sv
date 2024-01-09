// * * * Add defines structs enums * * * 

`define ACK           (1'b0)
`define NACK          (1'b1)
`define W             (1'b0)
`define R             (1'b1)
`define rev_put(a)    (7-a)
// `define START_BYTE    (8'b0000_0001)
// `define GENERAL_CALL  (8'b0000_0000)

typedef enum {MASTER, SLAVE} agent_type_enum;
typedef enum {WRITE, READ} transaction_type_enum;
typedef enum {
  WAIT_FOR_START,
  CHANGE_SPEED_MODE,
  ADDRESSING,
  WRITE, READ, 
  GENERAL_CALL_STATE, 
  CBUS_STATE, OTHER_BUS_STATE, FUTURE_PURPOSE_STATE, 
  DEVICE_ID_WRITE, DEVICE_ID_READ, 
  TEN_BIT_ADDR_WRITE, TEN_BIT_ADDR_READ
} scoreboard_state_enum;

typedef enum {PERIPHERAL_DEVICE, POLLING_CPU} slave_driver_type_enum;

typedef enum {SM, FM, FMP, HSM} speed_mode_enum;
typedef enum {FULL, HALF, QUARTER, QUANTUM} period_fraction_enum;

const bit[7:1] RESERVED_ADDRESSES[16] = {
  7'b000_0000, // General call or START Byte
  7'b000_0001, // C-Bus
  7'b000_0010, // Other Buses
  7'b000_0011, // Future Purpose
  7'b000_0100, 7'b000_0101, 7'b000_0110, 7'b000_0111, // Speed Modes
  7'b111_1100, 7'b111_1101, 7'b111_1110, 7'b111_1111, // Device ID
  7'b111_1000, 7'b111_1001, 7'b111_1010, 7'b111_1011 // 10-bit target addressing
};

const bit[7:0] GENERAL_CALL = 8'b0000_0000;
const bit[7:0] START_BYTE = 8'b0000_0001;

const bit[7:1] C-BUS = 7'b000_0001;
const bit[7:1] OTHER_BUSES = 7'b000_0010;
const bit[7:1] FUTURE_PURPOSE = 7'b000_0011;

const bit[7:3] SPEED_MODE = 5'b000_01;
const bit[7:3] DEVICE_ID = 5'b111_11;
const bit[7:3] TEN_BIT_TARGET_ADDRESSING = 5'b111_10;
