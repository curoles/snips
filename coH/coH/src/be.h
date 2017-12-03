/**@file
 * @brief
 * @author    Igor Lesik
 * @copyright Igor Lesik 2012
 *
 */
#pragma once
#ifndef COH_BE_H_INCLUDED
#define COH_BE_H_INCLUDED

#include <stdio.h>

struct AST;

#define EMIT(out, indent, frmt, ...)        \
    if(indent) fprintf(out, "%*s", (int)(indent<<2), " ");\
    fprintf(out, frmt, ##__VA_ARGS__ );

#define LN(frmt, ...) \
    EMIT(out, indent, frmt, ##__VA_ARGS__)


void
be_defClass(
    FILE* out,
    size_t indent,
    struct AST* ast
);

#endif //  COH_BE_H_INCLUDED
