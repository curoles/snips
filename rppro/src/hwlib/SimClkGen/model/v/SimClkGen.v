/**@file
 * @brief  Simple clock generator to use in RTL simulations.
 * @author Igor Lesik 2012
 */

module SimClkGen(
    output reg clk
);

integer count;

initial
begin
    count = 0;
    clk = 0;
end

always
begin
    #1 clk = ~clk;
    count = count + 1;
    //$display("Tick %d", count);
end

endmodule
