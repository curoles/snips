/**@file
 * @brief     Mig1 CPU 
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 */
module Mig1
#(
    parameter IMEM_ADDR_WIDTH = 32,
    parameter RF_ADDR_WIDTH = 9
)
(
    input clk,
    input reset,
    output [IMEM_ADDR_WIDTH-1:0] imem_addr,
    input [32-1:0] imem_data
);

    localparam WORD_WIDTH = 32;
    localparam WH = WORD_WIDTH-1;


    wire [WH:0] pc;
    wire is_branch;
    wire is_jump;

    ProgramCounter #(.WIDTH(WORD_WIDTH))
        _pc(
            .clk(clk),
            .reset(reset),
            .is_jump(is_jump),
            .is_branch(is_branch),
            .jump_size('h5),
            .pc(pc)
    );

    wire [WH:0] insn;

    FrontEnd #(.ADDR_WIDTH(32/*IMEM_ADDR_WIDTH*/), .INSN_WIDTH(WORD_WIDTH))
        _fe(
            .clk(clk),
            .reset(reset),
            .insn_addr(pc),
            .imem_addr(imem_addr),
            .imem_data(imem_data),
            .insn(insn)
    );

   wire [RF_ADDR_WIDTH-1:0] rf_addr_rd1;
   wire [RF_ADDR_WIDTH-1:0] rf_addr_rd2;
   wire [RF_ADDR_WIDTH-1:0] rf_addr_wr;
   wire rf_wr_enable;
   wire [WH:0] rf_rd1;
   wire [WH:0] rf_rd2;
   wire [WH:0] rf_wr;

    Decoder #(.INSN_WIDTH(WORD_WIDTH), .RF_ADDR_WIDTH(RF_ADDR_WIDTH))
        _decoder(
            .clk(clk),
            .reset(reset),
            .insn(insn),
            .is_branch(is_branch),
            .is_jump(is_jump),
            .rf_rd1(rf_addr_rd1),
            .rf_rd2(rf_addr_rd2),
            .rf_wr(rf_addr_wr),
            .rf_wr_enable(rf_wr_enable)
    );

    RegisterFile #(.WIDTH(WORD_WIDTH), .ADDR_WIDTH(RF_ADDR_WIDTH))
        _rf(
            .clk(clk),
            .reset(reset),
            .addr_rd1(rf_addr_rd1),
            .addr_rd2(rf_addr_rd2),
            .addr_wr(rf_addr_wr),
            .wr_enable(rf_wr_enable),
            .rd1(rf_rd1),
            .rd2(rf_rd2),
            .wr(rf_wr)
    );

    Executor #(.WIDTH(WORD_WIDTH))
        exe(
            .clk(clk),
            .reset(reset),
            .operand1(rf_rd1),
            .operand2(rf_rd2),
            .result(rf_wr)
    );


`define MONITOR_ENABLED
`ifdef MONITOR_ENABLED
    always @(clk) begin
        $display(
            "time:%3d clk:%d reset:%d pc:%h insn:%h",
            $time, clk, reset, pc, insn
        );
    end
`endif

endmodule
