/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_BE_DEF_FUN_H_INCLUDED
#define COH_BE_DEF_FUN_H_INCLUDED

#include "be.h"


void 
defFun(
    FILE* out,
    size_t indent,
    IrFunction* ir
)
{
    defClass(out, indent, &ir->class_in);
    defClass(out, indent, &ir->class_out);

    LN("void\n");
    LN("%s\n", ir->name.p);
    LN("(\n");
    LN("    %s * out,\n", ir->class_out.name.p);
    LN("    %s * in\n", ir->class_in.name.p);
    LN(")\n");
    LN("{\n");
    LN("}\n");
}

#endif //  COH_BE_DEF_FUN_H_INCLUDED
