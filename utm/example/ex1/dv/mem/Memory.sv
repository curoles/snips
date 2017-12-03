/**File:      Memory
 *
 * Brief:     SW Interface to a static memory.
 *
 * Author:    Igor Lesik 2015
 *
 * Copyright: Igor Lesik
 */

// Package: PkgMemory
package PkgMemory;

`define STATIC_ASSERT(cond)

/* Class: Memory
 *
 */
virtual class Memory
#(
    parameter int WORD_SIZE = 4, // 32-bit
    parameter int ADDR_SIZE = 32
);

    `STATIC_ASSERT (WORD_SIZE > 1 && WORD_SIZE < 17);

    typedef bit[ADDR_SIZE-1:0] Addr;

    typedef bit[7:0] Byte;
    typedef bit[WORD_SIZE-1:0] [7:0] Word;

    /* Function: readByte
     *
     * Parameters:
     *   addr - The address.
     *
     * Returns:
     *   Value at the address.
    */
    pure virtual function Byte readByte(Addr addr);

    pure virtual function Word readWord(Addr addr);

    pure virtual function bit readBit(Addr addr, int bitId);

    pure virtual function void writeByte(Addr addr, Byte byte8);

    pure virtual function void writeWord(Addr addr, Word word);

endclass: Memory

endpackage
