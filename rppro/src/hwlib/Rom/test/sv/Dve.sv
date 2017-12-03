`define MEM_FILE "memory.txt"

module Dve();

    localparam DW = 8;
    localparam AW = 8;

    wire  clk;

    reg  [AW-1:0] addr;
    wire [DW-1:0] data;

    SimClkGen clkgen(.clk(clk));

    Rom #(.ADDR_WIDTH(AW), .DATA_WIDTH(DW), .MEM_FILE(`MEM_FILE))
        rom(.clk(clk), .addr(addr), .data(data));


    initial
    begin

        addr = 'h0;

        $monitor("%2d clk:%h addr:%h data:%h", 
            $time, clk, addr, data);

        repeat(4)
        begin
            @(negedge clk);
            addr = addr + 1;
        end

        $finish();
    end


endmodule: Dve
