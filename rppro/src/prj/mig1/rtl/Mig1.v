/**@file
 * @brief
 * @author Igor Lesik
 *
 */


module Mig1(
    input clk,
    input reset_n
);

    localparam INSN_SIZE = 1 + 4;
    localparam INSN_WIDTH = INSN_SIZE * 8;

    parameter  I_ADDR_WIDTH = 16;

    Bus #(.WIDTH(INSN_WIDTH))   imem_data();
    Bus #(.WIDTH(I_ADDR_WIDTH)) imem_addr();

    Rom #(.ADDR_WIDTH(I_ADDR_WIDTH), .DATA_WIDTH(8), .DATA_SIZE(INSN_SIZE), .MEM_FILE(`MEM_FILE))
        rom(.clk(clk), .addr(imem_addr.bus), .data(imem_data.bus));


    wire insn_size;
    wire is_branch;

    Bus #(.WIDTH(I_ADDR_WIDTH)) pc_();

    ProgramCounter #(.WIDTH(I_ADDR_WIDTH))
        pc(
        .clk(clk),
        .reset_n(reset_n),
        .insn_size(insn_size),
        .is_branch(is_branch),
        .current_pc(imem_addr.bus),
        .new_pc(pc_.bus)
    );

    Bus #(.WIDTH(INSN_WIDTH)) insn_();

    FrontEnd #(.PC_WIDTH(I_ADDR_WIDTH), .INSN_WIDTH(INSN_WIDTH))
        fe(
        .clk(clk),
        .reset_n(reset_n),
        .new_pc(pc_.bus),
        .iaddr(imem_addr.bus),
        .idata(imem_data.bus),
        .insn(insn_.bus)
    );

    Executor #(.PC_WIDTH(I_ADDR_WIDTH), .INSN_WIDTH(INSN_WIDTH))
        exe(
        .clk(clk),
        .reset_n(reset_n),
        .insn(insn_.bus),
        .insn_size(insn_size),
        .is_branch(is_branch)
    );

endmodule
