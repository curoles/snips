/**@file
 * Symbol Table.
 *
 * Copyright (C) 2011 Igor Lesik.
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#include "symtbl.h"

Sym*
SymScope::
resolve(const char* symname)
{
    Sym* sym = members.get(symname);
    if (sym)
        return sym;

    if (getEnclosingScope()) {
        getEnclosingScope()->resolve(symname);
    }

    return NULL;
}

SymTbl::
SymTbl():SymPkg("global", NULL)
{
    initTypeSystem();
}

void
SymTbl::
initTypeSystem()
{

}
