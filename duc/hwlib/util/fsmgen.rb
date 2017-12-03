
module Fsm(in, out, clk, reset);

localparam SIZE = 2;
localparam NUM = 2**SIZE;

localparam IDLE = 2'b00;
parameter STATE2 = 2'b01;
parameter STATE3 = 2'b11;
parameter STATE4 = 2'b10;

input  clk;
input  reset;
input  in;
output out;

reg [1:0] current_state, next_state;

always @ (posedge ) begin
  if (reset == 1'b1)
    current_state <= IDLE;
  else
    current_state <= next_state;
end

always @ (current_state or sm_in)
begin
  // default values
  out = 1'b1;
  next_state = current_state;
  case (current_state)
  IDLE:
    sm_out = 1'b0;
    if (in)
      next_state = 2'b11;
  write:
sm_out = 1'b0;
if (sm_in == 1'b0)
next_state = 2'b10;
read:
if (sm_in == 1'b1)
next_state = 2'b01;
wait:
if (sm_in == 1'b1)
next_state = 2'b00;
endcase
end

endmodule
