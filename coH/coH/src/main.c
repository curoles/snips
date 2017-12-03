/**@file
 * @brief     Compiler main entry.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#include <stdlib.h>

#include "compiler.h"
#include "version.h"
#include "debug.h"
#include "cfg.h"


static void printBanner()
{
    PRINT("COH compiler %"PRIu64".%"PRIu64".%"PRIx64"\n",
        VER_MAJOR, VER_MINOR, VER_SUB);
    PRINT("by Igor Lesik\n");
}

//FIXME
extern int run_bc();

int main(int argc, char** argv)
{
    bool ok = false;

    LOG = stdout;

    Dbg_configure(LOG, DBG_L_NOISY, DBG_ALL);

    printBanner();

    //run_bc();//FIXME

    Compiler compiler;
    Compiler_create(&compiler);

    if (!Compiler_init(&compiler, argc, argv))
    {
        PRINT("Can't initialize compiler, exit.\n");
    }
    else if (String_isEmpty(&Cfg_input_file))
    {
        ok = true;
    }
    else
    {
        ok = Compiler_run(&compiler);
    }

    Compiler_destroy(&compiler);

    return ok? EXIT_SUCCESS : EXIT_FAILURE;
}

