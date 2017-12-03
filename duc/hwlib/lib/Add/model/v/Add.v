module Add #(parameter WIDTH = 8)
(
    input [WIDTH-1:0] in1;
    input [WIDTH-1:0] in2;
    input carry_in;
    output reg input carry_out;
    input add_sub,// if this is 1, add; else subtract
    output reg [WIDTH-1:0] result,
    input clk
);

    always @ (posedge clk)
    begin
        if (add_sub)
            {carry_out, result} <= in1 + in2 + carry_in;
        else
            {carry_out, result} <= in1 - in2 + carry_in;
    end

endmodule

/*
//http://en.wikibooks.org/wiki/Microprocessor_Design/Add_and_Subtract_Blocks

// 2 gates delay, compare to 3 gates in design with half-adders
module FullAdder (a,b,cin,cout,sum);

    input a, b, cin; // inputs
    output cout, sum; // output
    wire w1, w2, w3, w4; // internal nets

    xor (w1, a, b); 
    xor (sum, w1, cin);
    and (w2, a, b);
    and (w3, a, cin);
    and (w4, b, cin);
    or  (cout, w2, w3, w4);

endmodule

//Ripple Carry 4-bit Adder
module RippleCarryAdder4(A, B, cin, S, cout);
    input[3:0] A, B;
    input cin;
    output[3:0] S;
    output cout;

    wire c1, c2, c3;

    FullAdder fa0(A[0], B[0], cin, c1, S[0]);
    FullAdder fa1(A[1], B[1], c1, c2, S[1]);
    FullAdder fa2(A[2], B[2], c2, c3, S[2]);
    FullAdder fa3(A[3], B[3], c3, cout, S[3]);
endmodule
*/
