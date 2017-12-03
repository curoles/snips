/**
 * @brief     Mig1 Verilog Test Bench
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */
module Dve();

    localparam IMEM_ADDR_WIDTH = 8;

    integer clock_count = 0;

    wire clk;
    wire reset;

    wire [IMEM_ADDR_WIDTH-1:0] imem_addr;
    wire [32-1:0] imem_data;

    VRom #(.ADDR_WIDTH(IMEM_ADDR_WIDTH), .DATA_WIDTH(32), .DATA_SIZE(1))
        _rom(.addr(imem_addr>>2), .data(imem_data), .clk(clk));

    Mig1 #(.IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH))
        _cpu(.clk(clk), .reset(reset), .imem_addr(imem_addr), .imem_data(imem_data));

    initial
    begin
        $display("Mig1 Verilog Test Bench");


    end

    always @(posedge clk) begin
        if (clock_count > 12) begin
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
