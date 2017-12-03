/**@file
 * @brief     Verilog Test Bench for VRom
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 */

module Dve();

    localparam ADDR_WIDTH = 3;
    localparam DATA_WIDTH = 8;
    localparam DATA_SIZE = 1;
    localparam DATA_LEN = DATA_SIZE*DATA_WIDTH;

    reg  [ADDR_WIDTH-1:0] addr;
    wire [DATA_LEN-1:0] data;
    reg  clk;
    //reg  reset;

    VRom #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .DATA_SIZE(DATA_SIZE))
        rom(.addr(addr), .data(data), .clk(clk));

    integer clock_count = 0;

    initial
    begin
        $display("VRom Verilog TB");
        addr = 'h0;
    end

    always @(posedge clk) begin
        if (clock_count == 1) begin
            assert(data == 'h0);
            addr <= 'h0;
        end else if (clock_count == 3) begin
        end else if (clock_count == 4) begin
        end else if (clock_count == 5) begin
        end else if (clock_count == 6) begin
        end else if (clock_count > 10) begin
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
