/**@file
 * @brief     One-hot Multiplexer 
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */
module Mux1hot
#(parameter int unsigned INPUTS = 2,
  parameter int unsigned WIDTH  = 1)
(
  input  [WIDTH*INPUTS-1:0] in,
  input  [INPUTS-1:0]       sel,
  output [WIDTH-1:0]        out
);
  always_comb
  begin
    out = {WIDTH{1'b0}};
    for (int unsigned input_id = 0; input_id < INPUTS; input_id++)
    begin
      out |= {WIDTH{sel[input_id]}} & in[input_id*WIDTH +: WIDTH];
    end
  end
endmodule

module Mux1hot3 #(parameter WIDTH=1)
(
  input  [WIDTH-1:0]   in0,
  input  [WIDTH-1:0]   in1,
  input  [WIDTH-1:0]   in2,
  input  [3-1:0]       sel,
  output [WIDTH-1:0]   out
);

  Mux1hot #(.WIDTH(WIDTH), .INPUTS(3))
    mux1h3(.in{in2,in1,in0}, .sel(sel), .out(out));
endmodule
