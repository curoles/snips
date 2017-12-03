//http://www.sunburst-design.com/papers/CummingsSNUG2009SJ_SVA_Bind.pdf

// ERROR_Q_DID_NOT_FOLLOW_D: `assert_clk((q==$past(d)),1,"***ERROR!!***");

//`define assert_property(label, arg, error_enabled=0, msg="") \
//label: \
//assert property ( \
//    @(posedge clk) \
//    disable iff (reset) \
//    arg \
//) \
//else if(error_enabled==2) `uvm_error("ASSERT", msg); \
//else if(error_enabled) $error("%t: %m: %s", $time, msg)

`define assert_property(name, propbody, error_enabled=0, msg="") \
property property_``name ( \
    @(posedge clk) \
    disable iff (reset) \
    propbody \
) \
 \
assert_``name: \
assert property (property_``name) \
else if(error_enabled) $error("%t: %m: %s", $time, msg); \
 \
cover_``name: \
cover property (property_name) \
else $display({"property ",`"name`", " PASS"});
