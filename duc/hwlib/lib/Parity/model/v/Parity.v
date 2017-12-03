/**
 *
 *
Paper on parameterized models:
http://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-884-complex-digital-systems-spring-2005/related-resources/parameter_models.pdf

http://web.engr.oregonstate.edu/~traylor/ece474/lecture_verilog/beamer/verilog_operators.pdf
Verilog Reduction Operators
 - and(&), nand(~&), or(|), nor(~|) xor(^), xnor(^~,~^)
 - Operates on only one operand
 - Performs a bitwise operation on all bits of the operand
 - Returns a 1-bit result
 - Works from right to left, bit by bit

//let x = 4'b1010
&x //equivalent to 1 & 0 & 1 & 0. Results in 1'b0
|x //equivalent to 1 | 0 | 1 | 0. Results in 1'b1
^x //equivalent to 1 ^ 0 ^ 1 ^ 0. Results in 1'b0

A good example of the XOR operator is generation of parity.
*/

// Parity generator
// output is one if odd # of ones
//
module Parity #(parameter WIDTH=8)(
   input [WIDTH-1:0] in,
   output parity
);
   assign parity = ^in;
endmodule
