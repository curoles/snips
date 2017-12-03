// www.es.ele.tue.nl/mininoc/doc/rtl_systemc.pdf

#include "systemc.h"

SC_MODULE (Dff)
{
    sc_in<sc_logic>  inp;
    sc_out<sc_logic> outp;
    sc_in<sc_logic>  clk;

    SC_CTOR (Dff)
        : clk("clk"), inp("inp"), outp("outp")
    {
        SC_METHOD(flop);
        sensitive << clk.pos();

        //int some_int_param;
        //if (sc_get_param("some_int_param"), some_int_param);
    }
    
    void flop()
    {
        outp.write(inp.read());
    }

};

SC_MODULE_EXPORT (Dff);
