/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2013
 */


module FrontEnd
#(parameter ADDR_WIDTH = 32, parameter INSN_WIDTH = 32)
(
    input clk,
    input reset,
    input [ADDR_WIDTH-1:0] insn_addr,
    output /*reg*/ [ADDR_WIDTH-1:0] imem_addr,
    input [INSN_WIDTH-1:0] imem_data,
    output reg [INSN_WIDTH-1:0] insn
);
    localparam RESET_ADDR = 0;

    assign imem_addr = (reset)? RESET_ADDR : insn_addr;

    // Fetch instruction
    //
    always @(posedge clk)
    begin
        //$monitor("%2d clk:%h reset_n:%h pc:%h insn:%h", 
        //    $time, clk, reset_n, pc, insn);

        if (reset) begin
            //imem_addr <= RESET_ADDR;
            insn  <= 'h0; // NOP = 0
        end
        else begin
            $display("Fetching pc:%h insn:%h", imem_addr, imem_data);
            //imem_addr <= insn_addr;
            insn  <= imem_data;
        end
    end

endmodule
