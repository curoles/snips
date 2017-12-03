/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2013
 */

module Executor
#(parameter WIDTH = 32)
(
    input clk,
    input reset,
    input [WIDTH-1:0] operand1,
    input [WIDTH-1:0] operand2,
    output reg [WIDTH-1:0] result
);


    always @(posedge clk)
    begin

        if (reset)
        begin
            //
            //
        end
        else
        begin
            $display("Adding %h + %h", operand1, operand2);
            result <= operand1 + operand2;
        end
    end

endmodule
