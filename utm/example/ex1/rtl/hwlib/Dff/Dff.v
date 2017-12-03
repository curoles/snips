/**@file
 * @brief     Rising edge triggered D Flip Flop
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */


// Rising edge triggered D Flip Flop
//
module Dff #(parameter WIDTH=1)
(
  output reg [WIDTH-1:0] outp,
  input  [WIDTH-1:0] inp,
  input clk
);
   
  always @(posedge clk)
      outp[WIDTH-1:0] <= inp[WIDTH-1:0];

endmodule

