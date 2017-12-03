/**
 * @brief     Mig1 Test Bench
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */
module Dve();

    localparam IMEM_ADDR_WIDTH = 8;

    wire clk;
    wire reset;

    SimClkGen #(.PERIOD(1), .DEBUG(0)) _clk_gen(.clk(clk));
    SimRstGen #(.TIMEOUT(5)) _rst_gen(.clk(clk), .reset(reset));

    wire [IMEM_ADDR_WIDTH-1:0] imem_addr;
    wire [32-1:0] imem_data;

    VRom #(.ADDR_WIDTH(IMEM_ADDR_WIDTH), .DATA_WIDTH(32), .DATA_SIZE(1))
        _rom(.addr(imem_addr>>2), .data(imem_data), .clk(clk));

    Mig1 #(.IMEM_ADDR_WIDTH(IMEM_ADDR_WIDTH))
        _cpu(.clk(clk), .reset(reset), .imem_addr(imem_addr), .imem_data(imem_data));

    initial
    begin
        $display("Mig1 SV Test Bench");


        repeat(1200) begin
            @(posedge clk);
        end

        $finish();
    end

endmodule: Dve
