`ifndef MACRO_HELPERS_SVH_INCLUDED
`define MACRO_HELPERS_SVH_INCLUDED

// Usage: `DISPLAY(("format a=%x, b=%s", a, b));
// Note: "do" loop exists only in SystemVerilog.
`ifdef ENABLE_DISPLAY
    `define DISPLAY(msg) \
        do begin \
            /*$write("[%0t] %s:%d ", $time, `__FILE__, `__LINE__);*/ \
            $display msg; \
        end while(0)
`else
    `define DISPLAY(msg) \
         do begin end while(0)
`endif

// Usage inside a module:
// `static_assert_msg(N > 15, (1, "Parameter N has an invalid value of %0d", N))
//
`define static_assert_msg(condition, fatal_msg) \
generate \
if ( !(condition) ) $fatal fatal_msg; \
endgenerate

`define static_assert(condition) \
generate \
if ( !(condition) ) $fatal(1, `"condition`",,,"Assertion %m in %s:%0d", `__FILE__, `__LINE__); \
endgenerate


// Usage: always @(posedge clk ASYNC_POSEDGE_RESET(reset))
//
`define ASYNC_NEGEDGE_RESET(resetn) ,negedge resetn
`define ASYNC_POSEDGE_RESET(reset)  ,posedge reset

`endif // MACRO_HELPERS_SVH_INCLUDED

