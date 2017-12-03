

module IFU
#(
    parameter ADDR_WIDTH = 32,
    parameter WORD_SIZE = 4
)
(
    input clk,
    input reset,
    output reg read_request,
    output reg [ADDR_WIDTH-1:0] read_addr,
    input mem_read_data_ready,
    input [WORD_SIZE*8-1:0] mem_read_data
);

always @(posedge clk)
begin
    if (reset) begin
        read_request <= 0;
        read_addr <= '0;//helpers::fill_with_0();
    end
    else begin
        read_request <= 1;
        read_addr <= read_addr + 4;
    end
end


always @(posedge clk)
begin
    if (mem_read_data_ready) begin
        //$display("IFU read data=%x", mem_read_data);
    end
end

endmodule: IFU
