/**@file
 * Code Generator.
 *
 * Copyright Igor Lesik 2011.
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#pragma once
#ifndef HALO_CODEGEN_H_INCLUDED
#define HALO_CODEGEN_H_INCLUDED

#include "file.h"
#include "lvm/lcodegen.h"

class AST;

/** Code Generator parses AST and generates Symbol Table and code.
 *
 */
class CodeGen
{
public:
    CodeGen();
   ~CodeGen();

    bool run(File& f, AST& ast);

private:
    File m_file;
    LCodeGen m_gen;
    //ErrReport m_errReport;
    //AST       m_ast;
};

#endif
