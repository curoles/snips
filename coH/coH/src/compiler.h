/**@file
 * @brief     Compiler.
 * @author    Igor Lesik.
 * @copyright Igor Lesik 2011-2012.
 *
 */
#pragma once
#ifndef COH_COMPILER_H_INCLUDED
#define CON_COMPILER_H_INCLUDED

#include <stdbool.h>

#include "SrcRead.h"
#include "ErrReport.h"
#include "Scanner.h"
#include "Parser.h"
#include "ast.h"
#include "CodeGen.h"


struct Compiler
{
    SrcReader srcReader;
    ErrReport errReport;
    Scanner   scanner;
    Parser    parser;
    AST       ast;
    CodeGen   codegen;
};
typedef struct Compiler Compiler;

void Compiler_create(Compiler*);
bool Compiler_init(Compiler*, int argc, char** argv);
void Compiler_destroy(Compiler*);
bool Compiler_run(Compiler*);

#endif
