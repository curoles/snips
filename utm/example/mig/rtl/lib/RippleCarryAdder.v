`include "MacroHelpers.svh"

// Ripple Carry Adder
//
module RippleCarryAdder#(WIDTH = 4)
(
    input  [WIDTH-1:0] a,
    input  [WIDTH-1:0] b,
    input              cin,
    output [WIDTH-1:0] sum,
    output             cout
);
    `static_assert(WIDTH > 0);

    wire [WIDTH:0] w;
    assign w[0] = cin;
    assign cout = w[WIDTH];

    genvar i;

    generate
    for (i = 0; i < WIDTH; i= i+1)
    begin: CONNECT_FULL_ADDERS
        FullAdder fa(.a(a[i]), .b(b[i]), .cin(w[i]), .sum(sum[i]), .cout(w[i+1]));
    end
    endgenerate

endmodule

module RipleCarryAdderTester(
    input clk,
    input reset
);

localparam WIDTH = 16;

reg [WIDTH-1:0] a;
reg [WIDTH-1:0] b;
reg             cin;

wire [WIDTH-1:0] sum;
wire             cout;

integer unsigned count;

RippleCarryAdder#(.WIDTH(WIDTH)) adder(.*);

always @(posedge clk)
begin
    if (reset) begin
        count <= 0;
        a <= 0;
        b <= 0;
        cin <= 0;
    end
    else begin
        count <= count + 1;
        a <= count + 1;
        b <= count + 1;
        cin <= 0;
    end
end

assert property(
    @(posedge clk) disable iff (reset)
    (sum == count + count)      
) else $error("%0d != %0d + %0d", sum, count, count);


initial begin
    $monitor("count=%0d sum=%0d cout=%b", count, sum, cout);
end

endmodule

