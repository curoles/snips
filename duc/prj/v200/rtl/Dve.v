/**
 * @brief     V200 Verilog Test Bench
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */
module Dve();

    integer clock_count = 0;

    wire clk;
    wire reset;

    core core (
    .CLKEN('h1),
    .CLK2X(clk),
    .NATIVEPORRESET_n(~reset)
    );

    initial
    begin
        $display("V200 Verilog Test Bench");


    end

    always @(posedge clk) begin
        if (clock_count > 12000) begin
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
        reset = in_bool;
    endtask

endmodule: Dve
