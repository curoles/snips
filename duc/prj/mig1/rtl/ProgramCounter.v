/**@file
 * @brief
 * @author Igor Lesik
 *
 */

module ProgramCounter
#(parameter WIDTH = 32)
(
    input  clk,
    input  reset,
    input  is_jump,
    input  is_branch,
    input  [WIDTH-1:0] jump_size,
    output reg [WIDTH-1:0] pc
);
    localparam RESET_ADDR = 'h0;
    localparam BYTE_SIZE = 8; // 8 bits
    localparam DEFAULT_INCR = WIDTH / BYTE_SIZE;

    always @(posedge clk)
    begin
        //$monitor("%2d clk:%h reset:%h pc:%h", 
        //    $time, clk, reset, pc);

        if (reset) begin
            pc <= RESET_ADDR;
        end
        else begin
            pc <= ((is_jump)? 'h0 : pc) + ((is_jump || is_branch)? jump_size : DEFAULT_INCR);
        end
    end

endmodule
