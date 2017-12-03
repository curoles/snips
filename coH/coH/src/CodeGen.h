/**@file
 * @brief     Code Generator.
 * @author    Igor Lesik
 * @copyright Igor Lesik 2011-2012.
 *
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#pragma once
#ifndef COH_CODEGEN_H_INCLUDED
#define COH_CODEGEN_H_INCLUDED

#include <stdbool.h>
#include <stdio.h>

struct AST;

/** Code Generator parses AST and generates Symbol Table and code.
 *
 */
struct CodeGen
{

};
typedef struct CodeGen CodeGen;

void CodeGen_create(CodeGen* self);
void CodeGen_destroy(CodeGen* self);

bool CodeGen_run(CodeGen* self, struct AST* ast, FILE* fh, FILE* fc);

#endif
