/**@file
 * @brief  DUT simulation top.
 * @author Igor Lesik 2016
 */
`default_nettype none

import stdtype::*;

/// TB parameters.
///
class TbParams;
    localparam string name = "MigTB"; ///< TB name
endclass



module TbTop
#(
    parameter type tbParams = TbParams
);


    initial
    begin: unittest
        $display("%s: running stdtype::unittest", tbParams::name);
        stdtype::unittest();
        //$display("%s: running helpers::unittest", tbParams::name);
        //helpers::unittest();

    end: unittest


endmodule: TbTop
