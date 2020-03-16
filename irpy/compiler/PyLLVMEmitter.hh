#pragma once

#include "PyEmitter.hh"

#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/DebugInfoMetadata.h>

#include <algorithm>
#include <memory>

namespace irpy {

class PyLLVMEmitter : public PyEmitter
{
public:
    PyLLVMEmitter(std::ostream &stream, llvm::Module *module)
    	: PyEmitter(stream),
    	  module_(module)
    {
    }

    void emitModule(void);
    void emitMetadata(void);
    void emitBasicBlock(llvm::BasicBlock &bb);
    void emitStructType(const llvm::StructType &type);
   	void emitFunction(llvm::Function &func);
   	void emitGlobalVariable(const llvm::GlobalVariable &type);

private:

	llvm::Module *module_;
};

} // namespace irpy
