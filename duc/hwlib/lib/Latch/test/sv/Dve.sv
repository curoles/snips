/**
 * @brief     Latch TB
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */

module Dve();

    localparam WIDTH = 2;

    wire  clk;
    reg   enable;
    reg [WIDTH-1:0] in;
    wire [WIDTH-1:0] out;

    SimClkGen #(.PERIOD(1), .DEBUG(0)) clk_gen(.clk(clk));

    // can't bind because 'clk' is not input of Latch
    /*bind Latch*/ Latch_checker #(.WIDTH(WIDTH)) latch_checker(
        .in(in), .out(out), .enable(enable), .clk(clk)
    );
    Latch #(.WIDTH(WIDTH)) latch(.in(in), .out(out), .enable(enable));

    initial
    begin
        in = 'b10;
        enable = 1'b0;

        $monitor("%d clk:%h in:%h out:%h", 
            $time, clk, in, out);

        @(posedge clk);
        enable = 1'b1;

        repeat(5) begin
            @(posedge clk);
            in += 1;
        end

        $finish();
    end


endmodule: Dve
