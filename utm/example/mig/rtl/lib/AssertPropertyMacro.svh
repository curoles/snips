/* File: AssertPropertyMacro.svh
 *
 *
 * About:
 *   Brief     - Macros to simplify using SVA assertions.
 *   Author    - Igor Lesik 2016
 *   Copyright - Igor Lesik 2016
 *
 * See Also:
 *
 * <http://www.sunburst-design.com/papers/CummingsSNUG2009SJ_SVA_Bind.pdf>
 *
 * The paper is suggesting using macros to make assertions
 * a bit less verbose and easier to code.
 *
 * (start code)
 *
 * `define assert_property(label, arg, error_enabled=0, msg="") \
 * label: \
 * assert property ( \
 *     @(posedge clk) \
 *     disable iff (reset) \
 *     arg \
 * ) \
 * else if(error_enabled) $error("%t: %m: %s", $time, msg)
 *
 * (end)
 *
 * For Dff it can look like
 *
 * (start code)
 * ERROR_Q_DID_NOT_FOLLOW_D:
 *     `assert_clk((q==$past(d)),1,"***ERROR!!***");
 * (end)
 */


`ifdef SV_ENABLED

//`define assert_property(name, propbody, error_enabled=2, msg="ASSERT ERROR") \
//assert_``name: \
//assert property ( \
//    @(posedge clk) \
//    propbody \
//) \
//else if(error_enabled == 2) $fatal(1, "%t: %m: %s", $time, msg); \
//else if(error_enabled) $error("%t: %m: %s", $time, msg);

`define assert_property(name, propbody, error_enabled=2, msg="ASSERT ERROR") \
property property_``name; \
    @(posedge clk) \
    propbody \
endproperty \
 \
assert_``name: \
assert property (property_``name) \
else if(error_enabled == 2) $fatal(1, "%t: %m: %s", $time, msg); \
else if(error_enabled) $error("%t: %m: %s", $time, msg); \
 \
cover_``name: \
cover property (property_``name);


`else // Verilog not SV, so disable SVA

`define assert_property(name, propbody, error_enabled=0, msg="")

`endif
