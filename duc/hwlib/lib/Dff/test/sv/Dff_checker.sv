//http://www.sunburst-design.com/papers/CummingsSNUG2009SJ_SVA_Bind.pdf

/*program*/module Dff_checker(q, d, clk/*, rst*/);

  parameter WIDTH = 1;

  input  [WIDTH-1:0] d;   // data in
  input              clk;
  //input              rst;
  input  [WIDTH-1:0] q;   // data out

  integer clk_count = 0;

  property q_is_d;
    logic[WIDTH-1:0] v;
    @(posedge clk) (1,v=d) ##1 (q === v);
  endproperty

  assert property (q_is_d);

  assert property
    (@(posedge clk) $rose(d) |=> q);

  assert property
    (@(posedge clk) $fell(d) |=> !q);

ERROR_q_did_not_follow_d:
  assert property (@(posedge clk) disable iff (clk_count < 2) (q==$past(d)));

  //assert property (@(posedge clk) /*disable iff (rst)*/ (q==$past(d)))
  //else $display("ERROR: q did not follow d");

  always @(posedge clk) begin
    clk_count += 1;
  end

endmodule //program

