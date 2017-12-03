/**@file
 * @brief     Two input multiplexer 
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 *
 *       +------+
 * __a___| 1     \
 *       |        |___out___
 * __b___| 0      |
 *       |       /
 *       +---|--+
 *           |
 *         select
 *
 */
module Mux2 (a, b, select, out);
   
  parameter WIDTH = 1;

  input  [WIDTH-1:0] a;
  input  [WIDTH-1:0] b;
  input              select;

  output [WIDTH-1:0] out;

  reg    [WIDTH-1:0] out;
  
  always @(a or b or select)
      if (select)
          out = a;
      else
          out = b;

endmodule

