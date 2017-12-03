//http://www.sunburst-design.com/papers/CummingsSNUG2009SJ_SVA_Bind.pdf
//http://www.sunburst-design.com/papers/DAC2009_SystemVerilog_Update_Part2_SutherlandHDL.pdf

/* Module: DefaultAssertClkBlock
 *
 * This module does 2 things
 * - defines _global clock_ $global_clock
 * - disables assertions during reset and re-enables assertions after reset
 *
 * $global_clock could be used in
 * - property @($global_clock)
 * - always @($global_clock)
 */
module DefaultAssertClkBlock(
    input clk,  // this will be global clock $global_clock
    input reset
);


// Define _global clock_
default clocking DefaultClockingBlock @(posedge clk);
endclocking

always @(reset)
begin: always_turnoff_assertions_during_reset

  if (reset) begin
      $assertkill; $display("ASSERTIONS OFF during reset");
  end
  else begin
      $asserton; $display("ASSERTIONS ON");
  end

end

endmodule
