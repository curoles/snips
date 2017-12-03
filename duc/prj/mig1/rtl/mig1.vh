/**@file
 * @brief  MIG1 parameters.
 * @author Igor Lesik 2013
 *
 */
`ifndef MIG1_VH_INCLUDED
`define MIG1_VH_INCLUDED


// Usage: `MSG(("format a=%x, b=%s", a, b));
// Note: "do" loop exists only in SystemVerilog.
`ifdef MESSAGING
    `define MSG(msg) \
        do begin \
            /*$write("[%0t] %s:%d ", $time, `__FILE__, `__LINE__);*/ \
            $display msg; \
        end while(0)
`else
    `define MSG(msg) \
         do begin end while(0)
`endif



`endif // MIG1_VH_INCLUDED

