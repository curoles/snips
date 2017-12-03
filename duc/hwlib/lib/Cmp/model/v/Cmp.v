/**@file
 * @brief     Comparator
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */
module Cmp (in1, in2, eq);
   
  parameter WIDTH = 1;

  input [WIDTH-1:0] in1;
  input [WIDTH-1:0] in2;

  output [WIDTH-1:0] eq;

  assign eq = (in1 == in2);

endmodule

