/*
 * =====================================================================================
 * /
 * |     Filename:  concurrency_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/30/2013 09:52:03 AM
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
#include "llvm/ADT/APFloat.h"
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <map>

#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;


string itos(int n){
	stringstream ss; ss << n;
	return ss.str();
}

struct SeparateSync: public ModulePass {

	static char ID;
	SeparateSync() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fun){
			int n_sync = 0;
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_mutex_lock" || fnname == "pthread_mutex_unlock"){

					if( in == bb->begin() ){
						BasicBlock::iterator it_split = bb->begin(); it_split++;
						bb->splitBasicBlock(it_split);
						break;
					} else {
						n_sync++;
						BasicBlock::iterator it_split = in;
						bb->splitBasicBlock(it_split, fun->getName().str() + "_sync_" + itos(n_sync));
						break;
					}
				}

			}


		}}}


		return false;
	}
};


char SeparateSync::ID = 0;
static RegisterPass<SeparateSync> SeparateSync( "conc_sep", "Separate Concurrent accesses" );


