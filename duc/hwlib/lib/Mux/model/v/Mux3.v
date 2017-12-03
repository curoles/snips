/**@file
 * @brief     Three input multiplexer 
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 *
 *
 */
module Mux3 (a, b, c, select, out);
   
  parameter WIDTH = 1;

  input  [WIDTH-1:0] a;
  input  [WIDTH-1:0] b;
  input  [WIDTH-1:0] c;
  input  [1:0]       select;

  output [WIDTH-1:0] out;

  reg    [WIDTH-1:0] out;
  
  always @(a or b or c or select)
  begin
    case(select)
      2'b00: out = a;
      2'b01: out = b;
      default: out = c;
    endcase
  end
endmodule

