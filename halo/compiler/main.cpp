/**@file
 * Halo compiler main entry.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#include <stdlib.h>

#include "compiler.h"
#include "version.h"
#include "debug.h"

void printBanner()
{
    PRINT("Halo compiler %u.%u\n", VER_MAJOR, VER_MINOR);
}

int main(int argc, char** argv)
{
    Dbg::halo.setFlags(Dbg::ALL | Dbg::L2);

    printBanner();

    Compiler compiler;

    if (!compiler.init(argc, argv)) {
        PRINT("Can't initialize compiler, exit.\n");
        return EXIT_FAILURE;
    }

    return compiler.run()? EXIT_SUCCESS : EXIT_FAILURE;
}

