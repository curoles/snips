/**@file
 * @brief     Flip-Flop.
 * @author    Igor Lesik 2014-2016
 * @copyright Igor Lesik 2014-2016
 *
 */


/**
 * Module Dff
 * 
 * Rising edge triggered D Flip Flop.
 *
 * Template parameters:
 * #WIDTH - in/out signal width
 *
 *
 * @param clk input clock
 * @param in  input signal
 * @param out output signal
 *
 */
`include "AssertPropertyMacro.svh"

module Dff #(parameter WIDTH=1)
(
    input clk,
    input [WIDTH-1:0] in,
    output reg [WIDTH-1:0] out
);
   
    always @(posedge clk)
    begin
        out <= in;
    end

    `assert_property ( output_follows_input,
         out == $past(in)
     )

    // initial $monitor("Dff monitor @%0d %0d <- %0d", clk, out, in);

endmodule

