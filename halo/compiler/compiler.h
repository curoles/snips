/**@file
 * Compiler.
 * Copyright (C) 2011 Igor Lesik.
 *
 */
#pragma once
#ifndef HALO_COMPILER_H_INCLUDED
#define HALO_COMPILER_H_INCLUDED

#include "srcread.h"
#include "erreport.h"
#include "scan.h"
#include "parser.h"
#include "ast.h"
#include "codegen.h"

class Compiler
{
public:
    Compiler();
   ~Compiler();

    bool init(int argc, char** argv);
    bool run();

private:
    void generate();
    void printAST();

private:
    SrcReader m_srcReader;
    ErrReport m_errReport;
    Scanner   m_scanner;
    Parser    m_parser;
    AST       m_ast;
    CodeGen   m_codegen;
};

#endif
