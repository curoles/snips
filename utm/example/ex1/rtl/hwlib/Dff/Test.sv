/**
 * @brief     Dff TB
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */

module Dve;

    localparam WIDTH = 3;

    wire  clk;
    wire  reset;
    reg  [WIDTH-1:0] in;
    wire [WIDTH-1:0] out;

    SimClkGen#(.PERIOD(1), .DEBUG(0)) clk_gen(.clk(clk));
    SimRstGen#(.TIMEOUT(1))           rst_gen(.clk(clk), .reset(reset));

    Dff_checker#(.WIDTH(WIDTH)) dff_checker(
        .in(in), .out(out), .clk(clk), .reset(reset));

    Dff#(.WIDTH(WIDTH)) dff(.inp(in), .outp(out), .clk(clk));

    initial
    begin
        in = 'b00;

        $monitor("%d clk:%h in:%h out:%h", 
            $time, clk, in, out);

        repeat(5) begin
            @(posedge clk);
            //@(negedge clk); assert(out == in) else $fatal(1);
            in += 1;
        end

        $finish();
    end


endmodule: Dve
