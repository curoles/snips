/**@file
 * @brief     Verilog Test Bench for DFF
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */

module Dve();

    reg  d;
    wire q;
    reg  clk;
    //reg  reset;

    Dff #(.WIDTH(1)) dff(.d(d), .q(q), .clk(clk));

    integer clock_count = 0;

    initial
    begin
        $display("Dff Verilog TB");
        d = 1'b0;
    end

    always @(posedge clk) begin
        if (clock_count == 1) begin
            $display("set d=1");
            d <= 1;
        end else if (clock_count == 3) begin
            assert (q == d) $display ("OK. Q equals D");
            else $error("q != d");
        end else if (clock_count == 4) begin
            d <= 0;
        end else if (clock_count == 6) begin
            assert (q == d);
            d <= 1;
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
