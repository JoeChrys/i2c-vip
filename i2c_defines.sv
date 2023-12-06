// * * * Add defines structs enums * * * 

`define ACK         (1'b0)
`define NACK        (1'b1)
`define W           (1'b0)
`define R           (1'b1)
`define rev_put(a)  (7-a)
`define START_BYTE  (8'b0000_0001)

typedef enum {MASTER, SLAVE} agent_type_enum;
typedef enum {WRITE, READ} transaction_type_enum;
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
