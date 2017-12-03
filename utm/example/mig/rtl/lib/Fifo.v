/**
 * File: Fifo.v
 *
 * See <the source at file:Fifo.v.html>
 *
 * About:
 *   Brief     - Synchronous FIFO, one clock for read and write.
 *   Author    - Igor Lesik 2015
 *   Copyright - Igor Lesik 2015
 *
 */

/* Title: Diagram
 * 
 * (start code)
 * http://ditaa.sourceforge.net
 * <pre class="textdiagram" id="fifo">
 *
 *          +---------+       +-------------------------------------------+       +---------+
 *          |cBLU     |       |                                           |       |         |
 *  +------>|         +------>| Write Data                      Read Data +------>+         +------>
 *  Write   |         |       |                MEMORY                     |       |         | Read
 *  Data    |         |       | Write Address               Read Address  |       |         | Data
 *          |  Write  |       +-------------------------------------------+       |  Read   |
 *          |Interface|           ^                              ^                |Interface|
 *  +------>|         |           |                              |                |         |<-----+
 *   Write  |         |       +---------+     +----------+     +----------+       |         | Read
 *   Enable |         |       |Write    |     | Compare  |     | Read     |       |         | Enable
 *          |         +------>|Pointer  +---->| Logic    |<----+ Pointer  |<------+         |
 *          |         |       +---------+     +----------+     +----------+       |         |
 *          |         |                         |     |                           |         |
 *  <-------+         |<------------------------+     +-------------------------->+         +------>
 *   Full   |         |  Full                                             Empty   |         | Empty
 *          +---------+                                                           +---------+
 * </pre>
 * (end)
 *
 * See <the diagram at file:images/fifo.png>
 *
 */

/* Title: Design and Assertions
 *
 * http://www.sunburst-design.com/papers/CummingsSNUG2009SJ_SVA_Bind.pdf
 *
 * Six sample assertions that could be applied to the design to 
 * test the FIFO with respect to  correct operation when the FIFO is
 * either asynchronously reset or full/near-full conditions include:
 * - (1) When the FIFO is reset, the FIFO empty flag should be set and the 
 *   full flag, wptr (write pointer), rptr (read pointer) and cnt
 *   (word counter) should all be cleared.
 * - (2) If the word counter (cnt) is greater than FIFO_SIZE-1, the FIFO is full.
 * - (3) If the word counter (cnt) is less than FIFO_SIZE, the FIFO is not full.
 * - (4) If the word counter is FIFO_SIZE-1 and there is a write operation without
 *   a simultaneous read  operation, the FIFO should go full.
 * - (5) If the FIFO is full, and there is a write operation without
 *   a simultaneous read operation, the full flag should not change.
 * - (6) If the FIFO is full, and there is a write operation without
 *    a simultaneous read operation, the write pointer should not change.
*/

/* Module: Fifo
 *
 */
`include "AssertPropertyMacro.svh"

module Fifo
#(
    parameter DATA_WIDTH  = 8,
    parameter FIFO_P2SIZE = 4 //2^4=16
)
(
    input                       clk,        // Clock input
    input                       reset,      // Active high reset
    input      [DATA_WIDTH-1:0] data_in,    // Data input
    input                       rd_en,      // Read Enable
    input                       wr_en,      // Write Enable
    output reg [DATA_WIDTH-1:0] data_out,   // Data Output
    output                      fifo_empty, // FIFO empty
    output                      fifo_full   // FIFO full
);

localparam FIFO_SIZE = 2**FIFO_P2SIZE;
localparam ADDR_WIDTH = FIFO_P2SIZE;

reg [ADDR_WIDTH  :0] fifo_counter; // from 0 to FIFO_SIZE, so need more bits
reg [ADDR_WIDTH-1:0] wr_pointer;
reg [ADDR_WIDTH-1:0] rd_pointer;

reg [DATA_WIDTH-1:0] fifo_mem[FIFO_SIZE];

wire rd_ok, wr_ok; // ok = enable signal + conditions ok

assign fifo_full  = (fifo_counter == FIFO_SIZE);
assign fifo_empty = (fifo_counter == 0);

assign rd_ok = rd_en && !fifo_empty;
assign wr_ok = wr_en && !fifo_full;

// Control FIFO counter.
// - Set to 0 on during reset.
// - Do not update if read and write happen simultaneously.
// - +1 if write, -1 if read.
//
always @(posedge clk or posedge reset)
begin: FIFO_COUNTER
    if (reset) begin
        fifo_counter <= 0;
    end
    else if (wr_ok && !rd_ok) begin
        fifo_counter <= fifo_counter + 1;
    end
    else if(rd_ok && !wr_ok) begin
        fifo_counter <= fifo_counter - 1;
    end
end: FIFO_COUNTER


always @(posedge clk or posedge reset)
begin: WRITE_POINTER
    if (reset) begin
        wr_pointer <= 0;
    end
    else if (wr_ok) begin
        wr_pointer <= wr_pointer + 1;
    end
end: WRITE_POINTER


always @(posedge clk or posedge reset)
begin: READ_POINTER
    if (reset) begin
        rd_pointer <= 0;
    end
    else if (rd_ok) begin
        rd_pointer <= rd_pointer + 1;
    end
end: READ_POINTER


always @(posedge clk or posedge reset)
begin: READ_DATA
    if (reset) begin
        data_out <= 0;
    end
    else if (rd_ok) begin
        data_out <= fifo_mem[rd_pointer];
    end
end: READ_DATA

always @(posedge clk)
begin: WRITE_DATA
    if (wr_ok) begin
        fifo_mem[wr_pointer] <= data_in;
    end
end: WRITE_DATA

// See about checker
// http://www.sunburst-design.com/papers/DAC2009_SystemVerilog_Update_Part2_SutherlandHDL.pdf
checker FifoChecker;

let mutually_exlusive(a, b) = !(a && b);

CANT_BE_FULL_AND_EMPTY_AT_THE_SAME_TIME:
    assert property (
        @(posedge clk)
        disable iff (reset)
        mutually_exlusive(fifo_full, fifo_empty)
    );

    `assert_property ( FIFO_RESET_SHOULD_CAUSE_EMPTY1_FULL0_RPTR0_WPTR0_CNT0,
        reset |->
        (rd_pointer==0 && wr_pointer==0 && fifo_empty==1 && fifo_full==0 && fifo_counter==0)
     )

    // FIFO full condition assertions:
    `assert_property( FIFO_SHOULD_BE_FULL,
        disable iff(reset) fifo_counter > FIFO_SIZE-1 |-> fifo_full
    )
    `assert_property( FIFO_SHOULD_NOT_BE_FULL,
        fifo_counter < FIFO_SIZE |-> !fifo_full
    )
    `assert_property( FIFO_DID_NOT_GO_FULL,
        fifo_counter==FIFO_SIZE-1 && wr_en && !rd_en |=> fifo_full
    )
    `assert_property( FIFO_FULL__WRITE_CAUSED_FULL_FLAG_TO_CHANGE,
        fifo_full && wr_en && !rd_en |=> fifo_full
    )
    `assert_property( FIFO_FULL__WRITE_CAUSED_WPTR_TO_CHANGE,
        fifo_full && wr_en && !rd_en |=> $stable(wr_pointer)
    )

    // FIFO empty condition assertions:
    // TODO


endchecker

FifoChecker fifoChecker;

endmodule: Fifo



//`ifdef UNIT_TEST_ENABLED

/* Module: FifoTester
 *
 * TODO test both speed diffs causing full/empty conditions.
 */
module FifoTester(
    input clk,
    input reset
);

localparam DATA_WIDTH  = 32;
localparam FIFO_P2SIZE = 4; //2^4=16

reg       [DATA_WIDTH-1:0] data_in;    // Data input
reg                        rd_en;      // Read Enable
reg                        wr_en;      // Write Enable
reg       [DATA_WIDTH-1:0] data_out;   // Data Output
wire                       fifo_empty; // FIFO empty
wire                       fifo_full;  // FIFO full

integer unsigned count;

//let check_mutex(a, b) = assert( !(a && b) );

Fifo#(
    .DATA_WIDTH(DATA_WIDTH),
    .FIFO_P2SIZE(FIFO_P2SIZE)
) fifo(.*);


initial begin
    count = 0;
end

always @(posedge clk)
begin: WRITE_INTO_FIFO
    if (!fifo_full && !reset /*&& count[0]==1'b1*/) begin
        wr_en <= 1;
        data_in <= count;
        $display("FIFO tester writes %0d", count);
    end else begin
        wr_en <= 0;
    end
    count <= count + 1;
end

always @(posedge clk)
begin: READ_FROM_FIFO
    if (!fifo_empty && !reset && count[0]==1'b1) begin
        rd_en <= 1;
        //$display("FIFO tester reads");
    end else begin
        rd_en <= 0;
    end
end

initial begin
    $monitor("read=%0d full=%b empty=%b", data_out, fifo_full, fifo_empty);
end

endmodule
