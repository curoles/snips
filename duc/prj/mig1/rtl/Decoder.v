/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2013
 */

module Decoder
#(parameter INSN_WIDTH = 32, RF_ADDR_WIDTH = 9)
(
    input clk,
    input reset,
    input [INSN_WIDTH-1:0] insn,
    output reg is_branch,
    output reg is_jump,
    output reg [RF_ADDR_WIDTH-1:0] rf_rd1,
    output reg [RF_ADDR_WIDTH-1:0] rf_rd2,
    output reg [RF_ADDR_WIDTH-1:0] rf_wr,
    output reg rf_wr_enable
);


    // Decode instruction
    //
    always @(posedge clk)
    begin
        //$monitor("%2d clk:%h reset_n:%h insn:%h", 
        //    $time, clk, reset_n, insn);

        if (reset)
        begin
            is_branch    <= 1'b0;
            is_jump      <= 1'b0;
            rf_rd1       <= 'h0;
            rf_rd2       <= 'h0;
            rf_wr        <= 'h0;
            rf_wr_enable <= 'h0;
        end
        else begin
            $display("Decoding %b", insn);
            is_branch    <= 1'b0;
            is_jump      <= 1'b0;
            rf_rd1       <= 'h0;
            rf_rd2       <= 'h0;
            rf_wr        <= 'h0;
            rf_wr_enable <= 'h0;
        end
    end

endmodule
