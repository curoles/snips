

module MigCpu
#(
    parameter ADDR_WIDTH = CpuParams::ADDR_WIDTH,
    parameter WORD_SIZE  = CpuParams::WORD_SIZE,
    parameter WORD_WIDTH = CpuParams::WORD_WIDTH
)
(
    input clk,
    input reset,
    output mem_read_request,
    output [ADDR_WIDTH-1:0] mem_read_addr,
    input mem_read_data_ready,
    input [WORD_WIDTH-1:0] mem_read_data
);

IFU#(.ADDR_WIDTH(ADDR_WIDTH))
    ifu(.*, .read_request(mem_read_request), .read_addr(mem_read_addr));

endmodule: MigCpu
