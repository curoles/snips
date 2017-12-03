/**
 * File: stdtype.sv
 *
 * Standard convenient basic types.
 *
 * Author: Igor Lesik 2015
 *
 * Choice for the SV types is made based on TLM-2.0 choices.
 * See "UVM Guide Book": The data types of most members translate
 * directly into SystemVerilog. Bool and unsigned int in
 * SystemC become bit and int unsigned in SystemVerilog.
 * 
 *
 */

package stdtype;

    // Type: bool
    typedef enum bit {
        false = 0,  true = 1
    } bool;

    const bool YES   = true;
    const bool NO    = false;
    const bool ON    = true;
    const bool OFF   = false;
    const bool TRUE  = true;
    const bool FALSE = false;

    // Function: bool2string
    // Return string true|false based on the value.
    function string bool2string(bool val);
        return val.name;
    endfunction

    // Type: uint32
    typedef int unsigned uint32;

    // Type: int32
    typedef int unsigned int32;

    // Type: uint
    typedef int unsigned uint;

    // Type: uint64
    typedef longint unsigned uint64;

    // Type: int64
    typedef longint int64;

    // Type: uint16
    typedef shortint unsigned uint16;

    // Type: int16
    typedef shortint int16;

    // Type: uint8
    typedef byte unsigned uint8;

    // Type: int8
    typedef byte int8;

    // Constant: chandle_size
    const uint8 chandle_size = $bits(chandle);

    // Constant: CHANDLE_SIZE
    localparam uint8 CHANDLE_SIZE = $bits(chandle);

    // Enum: BitID
    // Provides constants like BIT0, BIT1, BIT2 ...
    typedef enum { BIT[0:127] } BitID;

    // Class: Any
    // Union template.
    class Any #(type T0 = int32, type T1 = int64,
                type T2 = int32, type T3 = int32, type T4 = int32);
        union tagged {T0 t0; T1 t1; T2 t2; T3 t3; T4 t4;} v;
    endclass

    // Function: get_bit
    // Get N's bit of an integer value.
    function bit get_bit(input int bit_id, input uint64 val);
        return 1'(val >> bit_id);
    endfunction

    // Class: BitStream
    // Bit-stream queue of some data type.
    class BitStream #(type Data);
        localparam DATA_SIZE = $bits(Data);
        typedef bit [DATA_SIZE-1:0] Bits;
        Bits stream[$];

        function void push(input Data d);
            push_bits(Bits'(d));
        endfunction

        function void push_bits(input Bits d);
            stream = {stream, d}; // append
        endfunction

        function Data pop();
            // convert stream back to a Data packet
            return Data'(pop_bits());
        endfunction

        function Bits pop_bits();
            automatic Bits d = stream[0]; // get first element
            stream = stream[1:$]; // remove packet from stream
            return d;
        endfunction

    endclass

    // Function: unittest, self-check unittest
    function void unittest(bool verbose = false);
        assert (bool2string(true) == "true");
        assert (bool2string(YES) == "true");
        assert (YES == true);
        assert (OFF == false);
        assert (ON == true);
        assert (type(TRUE) == type(bool));
        assert ($bits(uint32) == 32);
        assert ($bits(uint64) == 64);
        assert ($bits(uint16) == 16);
        assert ($bits(uint8) == 8);

        begin: iterate_bool_enum
            automatic bool b = b.first;
            do begin
                if (verbose) $display("%m: bool = %1d/%0s", b, b.name);
            end while ( (b = b.next) != b.first );
        end

        if (verbose) $display("%m: chandle size is %d", chandle_size);
        assert (chandle_size == CHANDLE_SIZE);

        assert (BitID'(0) == BIT0);
        assert (BIT7 == BitID'(7));
        begin
            automatic bit [0:2] v = 3'b010;
            assert (v[BIT0] == 0 && v[BIT1] == 1 && v[BIT2] == 0);
        end

        begin
            automatic Any#(int32,uint64) a = new;
            a.v.t0 = 1;
        end

        assert (get_bit(BIT0,5) == 1'b1 && get_bit(BIT1,5) == 1'b0 && get_bit(2,2+3) == 1'b1);

        begin
            typedef struct {
                uint16 address;
                reg [3:0] code;
                byte command [2];
            } Packet;
            automatic Packet q;
            automatic Packet p = Packet'{address:16'd7, code:4'd3, default: 0};
            automatic BitStream#(Packet) stream = new;
            stream.push(p);
            q = stream.pop();
            assert (q == p);
        end
    endfunction

endpackage: stdtype
//
//
//import Bool::*;
//class Cfg #(parameter isXEnabled = false);
//    localparam isYEnabled = false;
//endclass
//
//module Dut #(type Cfg)(input Cfg cfg);
//    bool y = Cfg::isYEnabled;
//endmodule: Dut
//
//module test;
//
//Cfg#(.isXEnabled(true)) cfg;
//Dut#(.Cfg(Cfg)) dut(.cfg(cfg));

//endmodule
