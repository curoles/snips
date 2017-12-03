/**@file
 * @brief
 * @author Igor Lesik
 *
 */

module ProgramCounter(
    clk,
    reset_n,
    insn_size,
    is_branch,
    current_pc,
    new_pc
);
    parameter WIDTH = 32;

    input clk;
    input reset_n;
    input insn_size;
    input is_branch;

    input  [WIDTH-1:0] current_pc;
    output [WIDTH-1:0] new_pc;

    assign new_pc = current_pc + 1;

/*
    output reg [WIDTH-1:0] pc;

    always @(posedge clk)
    begin
        //$monitor("%2d clk:%h reset_n:%h pc:%h", 
        //    $time, clk, reset_n, pc);

        if (~reset_n)
        begin
            pc <= 'h0;
        end
        else
        begin
            pc <= pc + 1;

        end
    end
*/
endmodule
