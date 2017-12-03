/**@file
 * @brief     D type Flip Flop with asynchronous reset
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */



//D type flip flop with asynchronous reset
//
module DffAsyncRst (q, d, clk, reset);
   
  parameter WIDTH = 1;

  input  [WIDTH-1:0] d;   // data in
  input              clk;
  input              reset;
  output [WIDTH-1:0] q;   // data out

  reg  [WIDTH-1:0] q;
  
  always @(posedge clk or posedge reset)
      if (reset)
          q[WIDTH-1:0] <= 'h0;
      else
          q[WIDTH-1:0] <= d[WIDTH-1:0];

endmodule

