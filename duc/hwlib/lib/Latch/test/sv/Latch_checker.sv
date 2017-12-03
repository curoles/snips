/**@file
 * @brief     Latch verification
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 */
program Latch_checker(in, out, enable, clk);

  parameter WIDTH = 1;

  input  [WIDTH-1:0] in;
  input  [WIDTH-1:0] out;
  input              enable;
  input              clk;


ERROR_out_did_not_follow_in:
  assert property (
    @(clk)
    disable iff (!enable)
    (out==in)
  );


endprogram

