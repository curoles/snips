/**@file
 * @brief  Clock signal generator to use in MG TBX RTL emulation.
 * @author Igor Lesik 2015
 */

/** Free running clock using special comment 'tbx clkgen'
 *
 */
module TbxEmuClkGen
#(
    parameter PERIOD = 1
)
(
    output reg clk
);

// tbx clkgen
initial
begin
    clk = 0;
    forever begin
        #PERIOD clk = ~clk;
    end
end

endmodule: TbxEmuClkGen
