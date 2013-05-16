/*
 * =====================================================================================
 * /
 * |     Filename:  optimization_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/15/2013 05:27:39 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */



#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Instructions.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Support/IRBuilder.h"
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdio.h>


#define mod_iterator(mod, fn) for( Module::iterator     fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn ) 
#define fun_iterator(fun, bb) for( Function::iterator   bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )


using namespace llvm;
using namespace std;




namespace {

	struct FillNames : public ModulePass {

		void put_operator_names( Module &M ){

			mod_iterator(M, fun){
				fun_iterator(fun,bb){
					blk_iterator(bb, in){

						if( UnaryInstruction::classof(in) ){
							if( !in->getOperand(0)->hasName() )
								in->getOperand(0)->setName("0");
							if( !in->hasName() )
								in->setName("0");
						}

						if( BinaryOperator::classof(in) ){
							if( !in->getOperand(0)->hasName() )
								in->getOperand(0)->setName("0");
							if( !in->getOperand(1)->hasName() )
								in->getOperand(1)->setName("0");
							if( !in->hasName() )
								in->setName("0");
						}

					}}}

		}


		void put_block_names( Module &M ){

			mod_iterator(M, fun){
				fun_iterator(fun,bb){
					if( !bb->hasName() )
						bb->setName("0");
				} }


		}

		static char ID;
		FillNames() : ModulePass(ID) {}
		virtual bool runOnModule(Module &M) {

			put_operator_names(M);
			put_block_names(M);

			return false;
		}
	};


	struct BinaryOp: public ModulePass {
		static char ID; // Pass identification, replacement for typeid
		BinaryOp() : ModulePass(ID) {}

		string operandname( Value* operand ){

			if( ConstantInt::classof(operand) ){

				ConstantInt* CI = dyn_cast<ConstantInt>(operand);
				int64_t val = CI->getSExtValue();
				stringstream nameop1_ss; nameop1_ss << "constant_" << val;
				return nameop1_ss.str();

			} else {
				return operand->getName().str();
			}

		}

		//LLVMValueRef llvmGenLocalStringVar(const char* data, int len){
			//LLVMValueRef glob = LLVMAddGlobal(mod, LLVMArrayType(LLVMInt8Type(), len), "string");

			//LLVMSetLinkage(glob, LLVMInternalLinkage);
			//LLVMSetGlobalConstant(glob, TRUE);

			//LLVMSetInitializer(glob, LLVMConstString(data, len, TRUE));

			//return glob;
		//}

		GlobalVariable* make_global_str(Module& M, string name){

			uint64_t length = (uint64_t) name.length()+1;
			//cerr << "---------------------" << name << "---------" << length << endl;
			ArrayType* ArrayTy_0 = ArrayType::get(IntegerType::get(M.getContext(), 8), length );

			GlobalVariable* gvar_array_a = new GlobalVariable(/*Module=*/M, 
					/*Type=*/ArrayTy_0,
					/*isConstant=*/false,
					/*Linkage=*/GlobalValue::ExternalLinkage,
					/*Initializer=*/0, // has initializer, specified below
					/*Name=*/"a");

			Constant* const_array_2 = ConstantArray::get(M.getContext(), name.c_str(), true);

			// Global Variable Definitions
			gvar_array_a->setInitializer(const_array_2);

			return gvar_array_a;

		}


Constant* pointerToArray( Module& M, GlobalVariable* global_var ){
	ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
	std::vector<Constant*> const_ptr_9_indices;
	const_ptr_9_indices.push_back(const_int64_10);
	const_ptr_9_indices.push_back(const_int64_10); 

	Constant* const_ptr_9 = ConstantExpr::getGetElementPtr(global_var, &const_ptr_9_indices[0], const_ptr_9_indices.size());
	return const_ptr_9;
}

		virtual bool runOnModule(Module &M) {

			mod_iterator(M, fn){
				fun_iterator(fn, bb){
					blk_iterator(bb, in){
						if( BinaryOperator::classof(in) ){



							string nameres = in->getName().str();
							string nameop1 = operandname( in->getOperand(0) );
							string nameop2 = operandname( in->getOperand(1) );


							GlobalVariable* c1 = make_global_str(M, nameres);
							GlobalVariable* c2 = make_global_str(M, nameop1);
							GlobalVariable* c3 = make_global_str(M, nameop2);



							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "binary_op" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in; insertpos++;




std::vector<Value*> params;
params.push_back(pointerToArray(M,c1));
params.push_back(pointerToArray(M,c2));
params.push_back(pointerToArray(M,c3));
CallInst* void_13 = CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);











							//CallInst* ci = CallInst::Create(InitFn, "", insertpos );

						}
					}
				}
			}

			return false;
		}
	};

}

char FillNames::ID = 0;
static RegisterPass<FillNames> X("fill_names", "Fills operands and Block Names");


char BinaryOp::ID = 0;
static RegisterPass<BinaryOp> Y("binary_op", "Instrument binary operations");

