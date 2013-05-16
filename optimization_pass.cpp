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
#include <stdio.h>


#define mod_iterator(mod, fn) for( Module::iterator     fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn ) 
#define fun_iterator(fun, bb) for( Function::iterator   bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )


using namespace llvm;







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


	struct Hello2 : public ModulePass {
		static char ID; // Pass identification, replacement for typeid
		Hello2() : ModulePass(ID) {}
		virtual bool runOnModule(Module &M) {

			//M.dump();
			mod_iterator(M, fn){
				fun_iterator(fn, bb){
					blk_iterator(bb, in){
						if(isa<BranchInst>(in)){
							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "call_fn" ,
										Type::getInt1Ty( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in;
							CallInst* ci = CallInst::Create(InitFn, "", insertpos );
							BranchInst* in_b = cast<BranchInst>(in);
							if( in_b->isConditional() )
								in_b->setCondition(ci);

						}

					}
				}
			}

			return false;
		}
	};

}

char FillNames::ID = 0;
static RegisterPass<FillNames> X("v_instrument", "Fills operands and Block Names");


char Hello2::ID = 0;
static RegisterPass<Hello2> Y("v_instrument2", "Hello2 World Pass");
