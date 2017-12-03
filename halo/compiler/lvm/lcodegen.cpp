/**@file
 * LLVM IR generator.
 *
 * Copyright Igor Lesik 2011.
 * License:   Distributed under the Boost Software License, Version 1.0.
 *            (See http://www.boost.org/LICENSE_1_0.txt)
 *
 */
#include "lvm/lcodegen.h"

#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/PassManager.h"
#include "llvm/CallingConv.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Assembly/PrintModulePass.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

LCodeGen::
LCodeGen()
{
    m_module = new llvm::Module("???", llvm::getGlobalContext());
}

LCodeGen::
~LCodeGen()
{
    delete m_module;
}

void
LCodeGen::
emit()
{
    verifyModule(*m_module, PrintMessageAction);

    PassManager pm;
    pm.add(createPrintModulePass(&outs()));
    pm.run(*m_module);

}

#if 0

  Constant* c = mod->getOrInsertFunction("mul_add",
  /*ret type*/                           IntegerType::get(getGlobalContext(),32),
  /*args*/                               IntegerType::get(getGlobalContext(),32),
                                         IntegerType::get(getGlobalContext(),32),
                                         IntegerType::get(getGlobalContext(),32),
  /*varargs terminated with null*/       NULL);
  
  Function* mul_add = cast<Function>(c);
  mul_add->setCallingConv(CallingConv::C);

  Function::arg_iterator args = mul_add->arg_begin();
  Value* x = args++;
  x->setName("x");
  Value* y = args++;
  y->setName("y");
  Value* z = args++;
  z->setName("z");

  BasicBlock* block = BasicBlock::Create(getGlobalContext(), "entry", mul_add);
  IRBuilder<> builder(block);

  Value* tmp = builder.CreateBinOp(Instruction::Mul,
                                   x, y, "tmp");
  Value* tmp2 = builder.CreateBinOp(Instruction::Add,
                                    tmp, z, "tmp2");

  builder.CreateRet(tmp2);


#endif
