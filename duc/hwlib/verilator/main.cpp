/**@file
 * @brief     Verilator user's top level to create the simulation executable
 * @author    Igor Lesik
 * @copyright Igor Lesik 2014
 *
 * see http://www.veripool.org/projects/verilator/wiki/Manual-verilator
 */
#include <verilated.h>
#include <svdpi.h>

#include "VDve.h"
#include "VDve__Dpi.h"

#define TOP_NAME "Dve"
#define TOP_SCOPE_NAME "Dve.v"

// Current simulation time
// This is a 64-bit integer to reduce wrap over issues and
// allow modulus.  You can also use a double, if you wish.
vluint64_t g_main_time = 0;
 
double sc_time_stamp () {   // Called by $time in Verilog;
    return g_main_time;     // converts to double, to match
}                           // what SystemC does

static
void chronos(VDve* top)
{
    svSetScope(svGetScopeFromName(TOP_SCOPE_NAME));

    set_clock(g_main_time & 0x1); // %2

    g_main_time++;            // Time passes...
}

static
void reset_sequence(VDve* top)
{
    assert(svGetScopeFromName(TOP_SCOPE_NAME));
    svSetScope(svGetScopeFromName(TOP_SCOPE_NAME));

    // assert reset
    set_reset(1);

    while (!Verilated::gotFinish()) {
        if (g_main_time > 10) {
            set_reset(0);   // Deassert reset
            break;
        }
        chronos(top);
        top->eval();
    }
}


int main(int argc, char **argv, char **env)
{
    // Remember args
    Verilated::commandArgs(argc, argv);

    // Create instance
    VDve top(TOP_NAME);

    Verilated::scopesDump();

    reset_sequence(&top);
 
    while (!Verilated::gotFinish()) {
        chronos(&top);
        top.eval();
    }

    top.final(); // Done simulating

    return 0;
}
