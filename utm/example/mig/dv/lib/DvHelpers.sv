package DvHelpers;

import stdtype::*;


class Array#(type ArrayT);

static function automatic
int sumElementsOfArray(ref ArrayT array, input int lo, input int hi);
    int mid = (lo + hi + 1) >> 1;
    assert(lo <= hi) else $fatal(1, "%0d <= %0d ? lo must be less_or_eq than hi", lo, hi);
    //$display("%d %d %d", lo, mid, hi);
    if (lo == hi)
        return array[lo];
    else if (lo + 1 == hi)
        return (array[lo] + array[hi]);
    else
        return (sumElementsOfArray(array,lo,mid-1) +
                sumElementsOfArray(array,mid,hi));
endfunction

endclass: Array

// Function: unittest, self-check unittest
function automatic void unittest(bool verbose = false);
    begin: test_sumElementsOfArray
        logic signed [31:0] array[5] = '{ 'd1, 'd2, 'd3, 'd4, 'd5};
        //Array#(type(array)) ai = new;
        assert (Array#(type(array))::sumElementsOfArray(array,0,4) == 15);
    end
endfunction

endpackage
