/**@file
 * @brief     Counter.
 * @author    Igor Lesik 2016
 * @copyright Igor Lesik 2016
 *
 * Counter that runs on "start" signal and automatically
 * stops once the counter counts to the end, that is overflows.
 */
`include "AssertPropertyMacro.svh"

/** Module AutoCounter.
 *
 * A counter with the start signal that automatically
 * stops counting when all bits are 1.
 */
module AutoCounter
#(
    parameter WIDTH = 4
)
(
    input clk,
    input reset,
    input start,
    output reg [WIDTH-1:0] count
);

    logic enable;   // internal enable signal for the counter
    logic overflow; // internal counter overflow flag


    always_latch begin // latch the start input signal
        if (reset)
            enable <= 0;
        else if (start)
            enable <= 1;
        else if (overflow)
            enable <= 0;
    end


    always @(posedge clk)
    begin
        if (reset)
            {overflow,count} <= 0;
        else
            {overflow,count} <= count + 1;
    end

    `assert_property ( increment_by_one_every_clock,
         iff (!reset && enable)
         {overflow,count} == $past(count) + 1
    )

endmodule
