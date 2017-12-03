/**
 * @brief     Parity TB
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */

module Dve();

    localparam WIDTH = 8;

    wire  clk;
    reg   [WIDTH-1:0] in;
    wire  parity;

    SimClkGen #(.PERIOD(1), .DEBUG(0)) clk_gen(.clk(clk));

    Parity #(.WIDTH(WIDTH)) parity_inst(.in(in), .parity(parity));

    initial
    begin
        in = 8'b10101010;

        $monitor("%d clk:%h in:%b parity:%h", 
            $time, clk, in, parity);

        //$system("date");
        @(posedge clk);

        repeat(5) begin
            @(posedge clk);
            assert(parity == (^in));
            in += 1;
        end
        //$system("date");

        $finish();
    end


endmodule: Dve
