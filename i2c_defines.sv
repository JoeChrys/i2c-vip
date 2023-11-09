// * * * Add defines structs enums * * * 

`define ACK         ('b0)
`define NACK        ('b1)
`define W           ('b0)
`define R           ('b1)
`define rev_put(a)  (7-a)

typedef enum {MASTER, SLAVE} agent_type_enum;
typedef enum {WRITE, READ} transaction_type_enum;
typedef enum {PERIPHERAL_DEVICE, POLLING_CPU} slave_driver_type_enum;

typedef enum {SM, FM, FMP, HSM} speed_mode_enum;
typedef enum {FULL, HALF, QUARTER, QUANTUM} period_fraction_enum;

// const int MAX_NUMBER_OF_ITEMS = 100;
