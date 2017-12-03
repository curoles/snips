/**@file
 * @brief     Dff verification
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 */
program Dff_checker
#(
    parameter WIDTH = 1
)
(
    input clk,
    input reset,
    input  [WIDTH-1:0] in,
    output [WIDTH-1:0] out
);

ERROR_output_does_not_follow_input:
  assert property (
    @(posedge clk)
    disable iff (reset)
    (out == $past(in))
  );

endprogram

