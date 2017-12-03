
module Dut
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

MigCpu migCpu(.*);

endmodule: Dut
