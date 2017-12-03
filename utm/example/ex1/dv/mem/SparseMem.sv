/**
 * File: SparseMem
 *
 */

`define STATIC_ASSERT(cond) localparam bit assert_`__LINE__ = cond? 0 : 1/0

// Package: PkgSram
package PkgSparseMem;

import PkgMemory::*;

/* Class: SparseMem
 *
 */
class SparseMem
#(
    parameter int WORD_SIZE = 4,
    parameter int ADDR_SIZE = 32

) extends Memory #(.WORD_SIZE(WORD_SIZE), .ADDR_SIZE(ADDR_SIZE));

   `STATIC_ASSERT (WORD_SIZE > 1 && WORD_SIZE < 17);

    Word mem [*];

    virtual function Byte readByte(Addr addr);
        return mem[addr / WORD_SIZE][addr % WORD_SIZE];
    endfunction

    virtual function Word readWord(Addr addr);
        return mem[addr / WORD_SIZE];
    endfunction

    virtual function bit readBit(Addr addr, int bitId);
        assert (bitId >=0 && bitId < 8);
        return mem[addr / WORD_SIZE][addr % WORD_SIZE][bitId];
    endfunction

    virtual function void writeByte(Addr addr, Byte byte8);
        mem[addr / WORD_SIZE][addr % WORD_SIZE] = byte8;
    endfunction

    virtual function void writeWord(Addr addr, Word word);
        mem[addr / WORD_SIZE] = word;
    endfunction


endclass: SparseMem

endpackage
