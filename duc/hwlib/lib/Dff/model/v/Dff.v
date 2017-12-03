/**@file
 * @brief     Rising edge triggered D Flip Flop
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */


// Rising edge triggered D Flip Flop
//
module Dff (q, d, clk);
   
  parameter WIDTH = 1;

  input  [WIDTH-1:0] d;   // data in
  input              clk;
  output [WIDTH-1:0] q;   // data out

  reg  [WIDTH-1:0] q;
  
  always @(posedge clk)
      q[WIDTH-1:0] <= d[WIDTH-1:0];

endmodule

//D type flip flop with asynchronous reset
//
/*
module Dff_asyncRst (q, d, clk, reset);
   
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
*/

// D type flip flop with synchronous reset
//
//always @ (posedge clk) if (reset) q <= 1'b0; else q <= d;
//
// Also can be done as (!reset & d) to d input of Dff



// D type flip flop with gated clock
//
//wire gtd_clk = enable && clk;
//always @ (posedge gtd_clk) q <= d;

//Data enabled D type flip flop
//
//always @ (posedge clk) if (enable) q <= d
//

// Negative edge triggered D type flip flop
//
//always @ (negedge clk) q <= d;
