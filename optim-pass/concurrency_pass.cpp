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

struct ChangePthreadC: public ModulePass {

	static char ID;
	ChangePthreadC() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if( fnname == "pthread_create" ){

					Function* fnc = cast<Function>(in_c->getArgOperand(2));
					Value* arg = in_c->getArgOperand(3);
					
					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(arg);
					CallInst::Create(fnc, params.begin(), params.end(), "", insertpos);
					
					
					
					

				}
			}
		}}}

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if( fnname == "pthread_create" ){
					instr_to_rm.push_back(in_c);
				}



			}


		}}}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
		


		return false;
	}
};

struct ChangeSync: public ModulePass {

	static char ID;
	ChangeSync() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){


				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_mutex_lock" || fnname == "pthread_mutex_unlock"){

					instr_to_rm.push_back(in);
					//in_c->dump();
					
					string mutexname = in_c->getArgOperand(0)->getName().str();

					GlobalVariable* c1 = make_global_str(M, mutexname);


					Value* InitFn = cast<Value> ( M.getOrInsertFunction(
								fnname == "pthread_mutex_lock"?"mutex_lock":"mutex_unlock" ,
								Type::getVoidTy( M.getContext() ),
								Type::getInt8PtrTy( M.getContext() ),
								(Type *)0
								));


					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
					CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);


				}

			}


		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}


		return false;
	}
};

struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		//{SeparateSync     pass;   pass.runOnModule(M);}
		//{ChangePthreadC   pass;   pass.runOnModule(M);}
		{ChangeSync       pass;   pass.runOnModule(M);}

		return false;
	}
};


char SeparateSync::ID = 0;
static RegisterPass<SeparateSync> SeparateSync( "conc_sep", "Separate Concurrent accesses" );

char ChangePthreadC::ID = 0;
static RegisterPass<ChangePthreadC> ChangePthreadC( "conc_pthread_c", "Annotate pthread_create calls");

char All::ID = 0;
static RegisterPass<All> All( "conc_all", "change calls to pthread_create");

char ChangeSync::ID = 0;
static RegisterPass<ChangeSync> ChangeSync( "conc_changesync", "change calls to mutex get/lock");

