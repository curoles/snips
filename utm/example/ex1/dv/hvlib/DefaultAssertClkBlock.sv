//http://www.sunburst-design.com/papers/CummingsSNUG2009SJ_SVA_Bind.pdf

module DefaultAssertClkBlock(
    input clk,
    input reset
);


default clocking DefaultClockingBlock @(posedge clk);
endclocking

always @(reset)
begin: always_turnoff_assertions_during_reset

  if (reset)  $assertkill;
  else        $asserton;

end

endmodule
