/**
 * @brief  ROM model
 * @author Igor Lesik 2013
 *
 * Binary format example:
 * @003
 * 00000011
 * 00000100
 * @005
 * 00000101
 * hex format example:
 * @003
 * 3
 * 4
 */

module VRom (
    addr,
    data,
    clk
 );
    parameter DATA_WIDTH = 8;
    parameter DATA_SIZE  = 1;
    localparam DATA_LEN = DATA_SIZE*DATA_WIDTH;
    parameter ADDR_WIDTH = 8;

    parameter MEM_FILE = "memory.txt";
    parameter MEM_FILE_HEX_FORMAT = 0;

    input  wire [(ADDR_WIDTH-1):0] addr;
    output reg  [(DATA_LEN  -1):0] data;
    input  wire                    clk;

    reg [DATA_WIDTH-1:0] rom [2**ADDR_WIDTH-1:0];  
 
    // Use $readmemb for binary and $readmemh for hexadecimal representation.
    //
    initial begin
        if (MEM_FILE_HEX_FORMAT)
            $readmemh(MEM_FILE, rom /*begin= , end=*/);
        else
            $readmemb(MEM_FILE, rom /*begin= , end=*/);
    end
 
    genvar i;
    generate for (i = 0; i < DATA_SIZE; i = i + 1)
    begin
        always @ (posedge clk)
        begin
            $display("ROM[%h]=%h", integer'(addr)+i, rom[integer'(addr)+i]);
            data[i*DATA_WIDTH +: DATA_WIDTH] <= rom[integer'(addr)+i];
        end
    end
    endgenerate

endmodule



/*
module Rom (
    input  [(ADDR_WIDTH-1):0] address,
    output [(DATA_WIDTH-1):0] data,
    input                     read_en,
    input                     chip_en
 );
    parameter DATA_WIDTH = 8;
    parameter ADDR_WIDTH = 8;
    parameter MEM_FILE = "memory.txt"
	
    reg [DATA_WIDTH-1:0] rom [2**ADDR_WIDTH-1:0];  

    assign data = (chip_en && read_en) ? rom[address] : 'h0;
  
    initial begin
        $readmemb(MEM_FILE, rom);
    end
  
endmodule: Rom
*/


/*
module Rom (
    input  [7:0] address,
    output [7:0] data,
    input        read_en,
    input        chip_en
 );
    reg [7:0] data;  

    always @ (chip_en or read_en or address)
    begin
      case (address)
        0 : data = 10;
        1 : data = 55;
        2 : data = 244;
        3 : data = 0;
        4 : data = 1;
        5 : data = 8'hff;
        6 : data = 8'h11;
        7 : data = 8'h1;
        8 : data = 8'h10;
        9 : data = 8'h0;
        10 : data = 8'h10;
        11 : data = 8'h15;
        12 : data = 8'h60;
        13 : data = 8'h90;
        14 : data = 8'h70;
        15 : data = 8'h90;
		default: data = 8'h00;
      endcase
    end
  
endmodule: Rom
*/
