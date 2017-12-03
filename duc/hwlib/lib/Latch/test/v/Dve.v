/**@file
 * @brief     Verilog Test Bench for Latch
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */

module Dve();

    reg  d;
    wire q;
    reg  clk;
    reg  enable;
    //reg  reset;

    Latch #(.WIDTH(1)) latch(.in(d), .out(q), .enable(enable));

    integer clock_count = 0;

    initial
    begin
        $display("Latch Verilog TB");
        enable = 1'b1;
    end

    always @(posedge clk) begin
        if (clock_count == 1) begin
            d <= 1;
        end else if (clock_count == 3) begin
            assert (q == d) $display ("OK. Q equals D");
            else $error("q != d");
        end else if (clock_count == 4) begin
            enable <= 0;
        end else if (clock_count == 5) begin
            d <= 0;
        end else if (clock_count == 6) begin
            assert (q != d);
            enable <= 1;
        end else if (clock_count > 10) begin
            assert (q == d);
            $display("Finish TB");
            $finish();
        end
    end

    export "DPI-C" task set_clock;

    task set_clock;
        input bit in_bool;
        clk = in_bool;
        if (clk) begin
            clock_count += 1;
            $display("Ticking %d", clock_count);
        end
    endtask

    export "DPI-C" task set_reset;

    task set_reset;
        input bit in_bool;
        //reset = in_bool;
    endtask

endmodule: Dve
