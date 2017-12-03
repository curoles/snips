/**@file
 * @brief  DUT simulation top.
 * @author Igor Lesik 2016
 */
`default_nettype none

import stdtype::*;

/// Class with DUT parameters.
///
class TbDutParams;
    localparam uint reset_timeout = 4; ///< reset period
endclass

/// DUT Top module.
///
module DutTop
#(
    parameter type params = TbDutParams
);

    localparam ADDR_WIDTH = CpuParams::ADDR_WIDTH;
    localparam WORD_SIZE  = CpuParams::WORD_SIZE;
    localparam WORD_WIDTH = CpuParams::WORD_WIDTH;

    wire  clk;
    wire  reset;
    wire mem_read_request;
    wire [ADDR_WIDTH-1:0] mem_read_addr;
    wire mem_read_data_ready;
    wire [WORD_WIDTH-1:0] mem_read_data;

    integer unsigned count;

    DefaultAssertClkBlock defaultAssertCB(.*);

    SimClkGen#(.PERIOD(1), .DEBUG(1))   clk_gen(.*);
    SimRstGen#(.TIMEOUT(params::reset_timeout))  rst_gen(.*);

    //FifoTester fifoTester(.*);
    //RipleCarryAdderTester adderTester(.*);

    Dut dut(.*);
    SimRam#(
        .ADDR_SIZE(ADDR_WIDTH), .WORD_SIZE(WORD_SIZE),
        .READ_MEM_FILE(1)
        )
        ram(.*,
            .read_en(mem_read_request), .addr(mem_read_addr),
            .data_ready(mem_read_data_ready), .read_data(mem_read_data)
    );

    initial
    begin
        count = 0;
        repeat(44) begin
            @(posedge clk);
            count++;
        end

        $finish();
    end

endmodule: DutTop
