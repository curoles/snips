/**@file
 * @brief
 * @author Igor Lesik
 *
 */

module Dve();

    wire  clk;
    reg   reset;


    SimClkGen clkgen(.clk(clk));

    Mig1 mig1(.clk(clk), .reset_n(~reset));

    initial
    begin

        //$monitor("%2d clk:%h addr:%h data:%h", 
        //    $time, clk, addr, data);

        reset = 1'b1;

        repeat(4)
        begin
            @(posedge clk);
        end

        reset = 1'b0;

        repeat(10)
        begin
            @(posedge clk);
        end

        $finish();
    end


endmodule: Dve
