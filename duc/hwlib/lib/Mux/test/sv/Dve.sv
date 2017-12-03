/**
 * @brief     Mux TB
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */

module Dve();

    localparam WIDTH = 3;
    localparam SIZE  = 3;
    localparam CHANNELS  = 2**SIZE;


    wire               clk;
    wire               reset;
    reg   [SIZE-1:0]   select;
    wire  [WIDTH-1:0]  out;
    reg   [(CHANNELS*WIDTH)-1:0] in;

    SimClkGen #(.PERIOD(1), .DEBUG(0)) clk_gen(.clk(clk));
    SimRstGen #(.TIMEOUT(1)) rst_gen(.clk(clk), .reset(reset));

    /*bind Mux*/ Mux_checker #(.WIDTH(WIDTH), .SIZE(SIZE)) mux_checker(
        .in(in), .out(out), .select(select), .clk(clk), .reset(reset)
    );
    Mux #(.WIDTH(WIDTH), .SIZE(SIZE))
        mux(.in(in), .out(out), .select(select));

    initial
    begin
        in = 'b111_110_101_100_011_010_001_000;
        select = 'h0;

        $monitor("%d clk:%h select:%h out:%h in:%b", 
            $time, clk, select, out, in);

        repeat(10) begin
            @(posedge clk);
            assert(out == select) else $fatal(1);
            select += 1;
        end

        $finish();
    end


endmodule: Dve
