package Test;

import PkgSram::Memory;
import PkgSram::Sram;
import PkgSparseMem::SparseMem;

localparam int WS = 4;

typedef Memory#(.WORD_SIZE(WS), .ADDR_SIZE(32)) TestMem;
typedef Sram#(.WORD_SIZE(WS), .ADDR_SIZE(32), .SIZE(1024)) TestSram;
typedef SparseMem#(.WORD_SIZE(WS), .ADDR_SIZE(32)) TestSparseMem;
typedef TestMem::Addr Addr;

class UnitTest;

    TestSram sram;
    TestSparseMem sparse;

    function new;
        sram = new;
        sparse = new;
    endfunction

    function int run();
        Addr addr = 7*WS;
        sram.writeWord(addr, 32'hdead_beef);
        assert ( sram.readWord(addr) == 32'hdead_beef );
        assert ( sram.readByte(addr) == 8'hef ) else $display("%h", sram.readByte(addr));
        assert ( sram.readByte(addr + 1) == 8'hbe );
        sram.writeByte(addr + 5, 8'b00000100);
        assert ( sram.readBit(addr + 5, 0) == 1'b0 );
        assert ( sram.readBit(addr + 5, 1) == 1'b0 );
        assert ( sram.readBit(addr + 5, 2) == 1'b1 );

        foreach (sram.mem[w]) begin
            sram.mem[w] = w;
            sparse.writeWord(w*WS, w);
        end
        for (int word = 0; word < 10; word++) begin
            $display("%h", sram.mem[word]);
            assert ( sram.mem[word] == word );
            assert ( sparse.readWord(word*WS) == word );
        end

        return 1;
    endfunction

endclass

endpackage


module Dve;

    Test::UnitTest ut;

    initial begin
        ut = new;
        assert (ut.run());
    end
endmodule


