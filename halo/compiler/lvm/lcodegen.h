/**@file
 * LLVM IR generator.
 *
 * Copyright Igor Lesik 2011.
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#pragma once
#ifndef HALO_LCODEGEN_H_INCLUDED
#define HALO_LCODEGEN_H_INCLUDED

namespace llvm { class Module; }

class LCodeGen
{
public:
    LCodeGen();
   ~LCodeGen();

   void emit();

private:
    llvm::Module* m_module;
};

#endif
