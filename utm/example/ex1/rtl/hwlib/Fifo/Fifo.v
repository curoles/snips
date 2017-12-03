/**
 * File: Fifo.v
 *
 * Synchronous FIFO, one clock for read and write.
 *
 * Author: Igor Lesik 2015
 *
 * Copyright: Igor Lesik 2015
 *
 * 
 * http://ditaa.sourceforge.net

          +---------+       +-------------------------------------------+       +---------+
          |         |       |                                           |       |         |
  +------>|         +------>| Write Data                      Read Data +------>+         +------>
  Write   |         |       |                MEMORY                     |       |         | Read
  Data    |         |       | Write Address               Read Address  |       |         | Data
          |  Write  |       +-------------------------------------------+       |  Read   |
          |Interface|           ^                              ^                |Interface|
  +------>|         |           |                              |                |         |<-----+
   Write  |         |       +---------+     +----------+     +----------+       |         | Read
   Enable |         |       |Write    |     | Compare  |     | Read     |       |         | Enable
          |         +------>|Pointer  +---->| Logic    |<----+ Pointer  |<------+         |
          |         |       +---------+     +----------+     +----------+       |         |
          |         |                         |     |                           |         |
  <-------+         |<------------------------+     +-------------------------->+         +------>
   Full   |         |  Full                                             Empty   |         | Empty
          +---------+                                                           +---------+


 */


/* Module: Fifo
 *
 */
module Fifo
#(
    parameter DATA_WIDTH  = 8,
    parameter FIFO_P2SIZE = 4, //2^4=16
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

reg [ADDR_WIDTH-1:0] fifo_counter;
reg [ADDR_WIDTH-1:0] wr_pointer;
reg [ADDR_WIDTH-1:0] rd_pointer;

reg [DATA_WIDTH-1:0] fifo_mem[FIFO_SIZE];

wire rd_ok, wr_ok; // enable signal and conditions ok

//? always @(fifo_counter)
assign fifo_full  = (fifo_counter == FIFO_SIZE);
assign fifo_empty = (fifo_counter == 0);
assign rd_ok = rd_en && !fifo_empty;
assign wr_ok = wr_en && !fifo_full;

always @(posedge clk or posedge rst)
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
        fifo_mem[wr_ptr] <= data_in;
    end
end: WRITE_DATA

endmodule: Fifo

