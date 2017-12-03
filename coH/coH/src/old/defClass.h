/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_BE_DEF_CLASS_H_INCLUDED
#define COH_BE_DEF_CLASS_H_INCLUDED

#include <stdio.h>
#include <stddef.h>

#include "ir.h"

void 
defClass(
    FILE* out,
    size_t indent,
    IrClass* ir
);

#endif //  COH_BE_DEF_CLASS_H_INCLUDED
