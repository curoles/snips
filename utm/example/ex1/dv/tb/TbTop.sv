`default_nettype none

import stdtype::*;

`define TB_NAME(module_name) E1``module_name

class TbParams;
    localparam string name = "E1";
    localparam uint   reset_timeout = 10;
endclass



module `TB_NAME(TbTop)
    #(parameter type params = TbParams);

    wire  clk;
    wire  reset;

    SimClkGen#(.PERIOD(1), .DEBUG(1))   clk_gen(.*);
    SimRstGen#(.TIMEOUT(params::reset_timeout))  rst_gen(.*);

    initial
    begin: unittest
        $display("%s: running unittest", params::name);
        stdtype::unittest();
    end: unittest

    initial
    begin
        repeat(11) begin
            @(posedge clk);
        end

        $finish();
    end

endmodule: `TB_NAME(TbTop)
