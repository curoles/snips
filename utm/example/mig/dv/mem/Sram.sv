/**
 * @file
 * @brief     SRAM model.
 * @author    Igor Lesik 2016
 * @copyright Igor Lesik
 */

//`include "rtl/lib/MacroHelpers.svh"

/// Package SramPkg
package SramPkg;

import MemoryPkg::*;

/* Class: Sram
 *
 */
class Sram
#(
    parameter int WORD_SIZE = 4,
    parameter int ADDR_SIZE = 32,
    parameter int SIZE = 1024 // in bytes

) extends Memory #(.WORD_SIZE(WORD_SIZE), .ADDR_SIZE(ADDR_SIZE));

   //`static_assert (WORD_SIZE >= 1 && WORD_SIZE < 17)


    Word mem [SIZE/WORD_SIZE];

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


endclass: Sram

endpackage
