/**@file
 * @brief  Simple clock generator to use in RTL simulations.
 * @author Igor Lesik 2012
 */

/** Module SimClkGen
 *
 *
 */
module SimClkGen
#(
    parameter PERIOD = 1, ///< number or time (5ns)
    parameter DEBUG  = 0  ///< turn on debug messages via $display
)
(
    output reg clk ///< generated clock signal
);

    integer unsigned count = 0;

    initial
    begin
        clk = 0;
    end
    
    always
    begin
        #PERIOD clk = ~clk;
        count += 1;
        if (DEBUG)
        begin
            $display("%t %d tick", $time, count);
        end
    end

endmodule

