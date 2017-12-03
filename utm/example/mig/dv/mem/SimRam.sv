/**
 * @file
 * @brief     Simulation SRAM model.
 * @author    Igor Lesik 2016
 * @copyright Igor Lesik
 */


module SimRam
#(
    parameter WORD_SIZE = 1,
    parameter ADDR_SIZE = 32,
    parameter SIZE = 1024,

    parameter READ_MEM_FILE = 0,
    parameter MEM_FILE = "memory.txt",
    parameter MEM_FILE_HEX_FORMAT = 1
)
(
    input clk,
    input read_en,
    input [ADDR_SIZE-1:0] addr,
    output reg [WORD_SIZE*$bits(byte)-1:0] read_data,
    output reg data_ready
);

typedef SramPkg::Sram#(
    .WORD_SIZE(WORD_SIZE), .ADDR_SIZE(ADDR_SIZE), .SIZE(SIZE)) Sram;

Sram sram = new;

always @(posedge clk)
begin
    if (read_en) begin
        $display("SimRam read addr=%x", addr);
        read_data <= sram.readWord(addr);
        data_ready <= 1;
    end
    else begin
        read_data <= 'x;
        data_ready <= 0;
    end
end

// Initialize memory from file.
// Use $readmemb for binary and $readmemh for hexadecimal representation.
//
initial begin
    if (READ_MEM_FILE) begin
        if (MEM_FILE_HEX_FORMAT)
            $readmemh(MEM_FILE, sram.mem /*begin= , end=*/);
        else
            $readmemb(MEM_FILE, sram.mem /*begin= , end=*/);
    end
end

endmodule
