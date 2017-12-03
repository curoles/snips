/**@file
 * @brief     Multiplexer 
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 *
 *
 */


module Mux (in, select, out);
   
  parameter WIDTH = 1;
  parameter SIZE  = 1;
  parameter CHANNELS  = 2**SIZE;

  input  [(CHANNELS*WIDTH)-1:0] in;
  input  [SIZE-1:0]   select;

  output [WIDTH-1:0] out;


  genvar ig;
    
  wire [WIDTH-1:0] input_array [0:CHANNELS-1];

  assign out = input_array[select];

  generate
    for(ig=0; ig < CHANNELS; ig=ig+1) begin: array_assignments
      assign input_array[ig] = in[(ig*WIDTH)+:WIDTH];
      // use [((ig+1)*WIDTH)-1:(ig*WIDTH)] if +: not supported
    end
  endgenerate

endmodule

