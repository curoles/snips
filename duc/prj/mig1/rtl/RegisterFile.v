/**@file
 * @brief     Register File
 * @author    Igor Lesik
 * @copyright Igor Lesik 2013
 */

module RegisterFile
#(parameter WIDTH = 32, parameter ADDR_WIDTH = 9)
(
    input clk,
    input reset,
    input [ADDR_WIDTH-1:0] addr_rd1,
    input [ADDR_WIDTH-1:0] addr_rd2,
    input [ADDR_WIDTH-1:0] addr_wr,
    input wr_enable,
    output reg [WIDTH-1:0] rd1,
    output reg [WIDTH-1:0] rd2,
    input [WIDTH-1:0] wr
);

    localparam SIZE = 2**ADDR_WIDTH;

    reg [WIDTH-1:0] rf [0:SIZE-1];

    // Decode instruction
    //
    always @(posedge clk)
    begin

        if (reset)
        begin
            //rd1 <= 'h0;
            //rd2 <= 'h0;
        end
        else begin
            $display("Read RF %h %h", addr_rd1, addr_rd2);
            rd1 <= rf[addr_rd1];
            rd2 <= rf[addr_rd2];
            if (wr_enable) begin
                rf[addr_wr] <= wr;
            end
        end
    end

endmodule
