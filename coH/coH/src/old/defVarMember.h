/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_BE_DEF_VAR_MEMBER_H_INCLUDED
#define COH_BE_DEF_VAR_MEMBER_H_INCLUDED

#include "be.h"
#include "ir.h"

void 
defVarMember(
    FILE* out,
    size_t indent,
    IrClassMemberVar* ir
)
{
    LN("%s %s;\n",
        ir->type.p,
        ir->name.p
    );
}

#endif //  COH_BE_DEF_VAR_MEMBER_H_INCLUDED
