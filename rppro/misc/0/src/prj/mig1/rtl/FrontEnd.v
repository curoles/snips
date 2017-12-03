/**@file
 * @brief
 * @author Igor Lesik
 * @copyright Igor Lesik 2013
 */


module FrontEnd(
    clk,
    reset_n,
    new_pc,
    iaddr, // current PC
    idata,
    insn
);

    parameter PC_WIDTH = 16;
    parameter INSN_WIDTH = 40;

    input clk;
    input reset_n;

    input      [PC_WIDTH-1:0]   new_pc;
    output reg [PC_WIDTH-1:0]   iaddr;
    input      [INSN_WIDTH-1:0] idata;
    output reg [INSN_WIDTH-1:0] insn;

    // Fetch instruction
    //
    always @(posedge clk)
    begin
        //$monitor("%2d clk:%h reset_n:%h pc:%h insn:%h", 
        //    $time, clk, reset_n, pc, insn);

        if (~reset_n)
        begin
            iaddr <= 'h0;
            insn  <= idata;
        end
        else
        begin
            $display("Fetching pc:%h insn:%h", new_pc, idata);
            iaddr <= new_pc;
            insn  <= idata;
        end
    end

endmodule
