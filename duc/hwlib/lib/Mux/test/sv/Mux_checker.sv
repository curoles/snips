/**@file
 * @brief     Mux verification
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 */
program Mux_checker(in, out, select, clk, reset);

  parameter WIDTH = 1;
  parameter SIZE  = 1;
  parameter CHANNELS  = 2**SIZE;

  input  [(CHANNELS*WIDTH)-1:0] in;
  input  [WIDTH-1:0] out;
  input  [SIZE-1:0]  select;
  input              clk;
  input              reset;


ERROR_out_is_not_selected_in:
  assert property (
    @(clk)
    disable iff (reset)
    (out==in[select*WIDTH +: WIDTH])
  );


endprogram

