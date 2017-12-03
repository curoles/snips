/**
 * @brief     ROM model TB
 * @author    Igor Lesik 2014
 * @copyright Igor Lesik 2014
 */

module Dve();

    localparam ADDR_WIDTH = 3;
    localparam DATA_WIDTH = 8;

    wire  clk;
    wire  reset;
    wire [DATA_WIDTH-1:0] data;
    reg  [ADDR_WIDTH-1:0] addr;

    SimClkGen #(.PERIOD(1)) clk_gen(.clk(clk));
    SimRstGen rst_gen(.clk(clk), .reset(reset));

    VRom #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH))
        rom(.data(data), .addr(addr), .clk(clk));

    initial
    begin
        addr = 'h0;

        $monitor("%d rst:%h clk:%h addr:%h data:%h", 
            $time, reset, clk, addr, data);

        @(negedge reset);

        repeat(5) begin
            @(posedge clk); // start sampling address
            @(negedge clk); // give some time to sample
            assert(data[ADDR_WIDTH-1:0] == addr)
            else begin
                $display("addr=%h data=%h", addr, data);
                //$fatal(1);
            end
            addr += 1;
        end

        $finish();
    end


endmodule: Dve
