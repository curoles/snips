/**@file
 * @brief  Verilog macro to wrap-up $display.
 * @author Igor Lesik 2012
 *
 * Note: do-while is SystemVerilog construct,
         it does not exist in Verilo.
 */
`ifndef DBG_DISPLAY_SVH_INCLUDED
`define DBG_DISPLAY_SVH_INCLUDED

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



`endif

