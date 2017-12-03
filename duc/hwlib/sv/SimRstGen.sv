/**@file
 * @brief  Simple reset signal generator to use in RTL simulations.
 * @author Igor Lesik 2012
 */

module SimRstGen(
    input clk,
    output reg reset
);

    parameter TIMEOUT = 1;

    integer count = 0;

    initial
    begin
        reset = 1;
    end
    
    always @(posedge clk)
    begin
        count += 1;
        if (count > TIMEOUT)
            reset <= 0;
        else
            reset <= 1;
    end

endmodule
