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

		virtual bool runOnModule(Module &M) {

			mod_iterator(M, fn){
				fun_iterator(fn, bb){
					blk_iterator(bb, in){
						if( BinaryOperator::classof(in) ){



							string nameres = in->getName().str();
							string nameop1 = operandname( in->getOperand(0) );
							string nameop2 = operandname( in->getOperand(1) );

							cerr << "\033[31m " << nameres << "\033[0m" << endl;
							cerr << "\033[31m " << nameop1 << "\033[0m" << endl;
							cerr << "\033[31m " << nameop2 << "\033[0m" << endl;


							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "binary_op" ,
										Type::getVoidTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in; insertpos++;
							CallInst* ci = CallInst::Create(InitFn, "", insertpos );





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

