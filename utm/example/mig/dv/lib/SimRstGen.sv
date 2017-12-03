/**@file
 * @brief  Simple reset signal generator to use in RTL simulations.
 * @author Igor Lesik 2012
 */

module SimRstGen
#(
    parameter TIMEOUT = 1
)
(
    input clk,
    output reg reset
);
    integer count = 0;
    // reset = 0 TODO Initialize to inactive state! In case someone looking @posedge reset

    initial
    begin
        reset <= 1;
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
