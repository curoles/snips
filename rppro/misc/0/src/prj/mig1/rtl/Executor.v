/**@file
 * @brief
 * @author Igor Lesik
 * @copyright Igor Lesik 2013
 */

module Executor(
    clk,
    reset_n,
    insn,
    insn_size,
    is_branch
    //branch_pc
);

    parameter PC_WIDTH = 16;
    parameter INSN_WIDTH = 40;

    input clk;
    input reset_n;

    output reg insn_size;
    output reg is_branch;

    //output reg [PC_WIDTH-1:0]   next_pc;
    //output reg [PC_WIDTH-1:0]   iaddr;
    //input      [INSN_WIDTH-1:0] idata;
    input [INSN_WIDTH-1:0] insn;

    // Decode instruction
    //
    always @(posedge clk)
    begin
        //$monitor("%2d clk:%h reset_n:%h insn:%h", 
        //    $time, clk, reset_n, insn);

        if (~reset_n)
        begin
            //
            //
            is_branch <= 1'b0;
            insn_size <= 1'b0;
        end
        else
        begin
            $display("Decoding %h", insn);
            //
            //
            is_branch <= 1'b0;
            insn_size <= 1'b0;
        end
    end

endmodule
