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
			int n_sync = -1;
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_mutex_lock" || fnname == "pthread_mutex_unlock"){

					n_sync++;

					if( in == bb->begin() ){
						bb->setName(fun->getName().str() + "_sync_" + itos(n_sync));
						BasicBlock::iterator it_split = bb->begin(); it_split++;
						bb->splitBasicBlock(it_split);
						break;
					} else {
						BasicBlock::iterator it_split = in;
						bb->splitBasicBlock(it_split, fun->getName().str() + "" + itos(n_sync));
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
					string syncname  = bb->getName().str();

					GlobalVariable* c1 = make_global_str(M, mutexname);
					GlobalVariable* c2 = make_global_str(M, syncname);


					Value* InitFn = cast<Value> ( M.getOrInsertFunction(
								fnname == "pthread_mutex_lock"?"mutex_lock":"mutex_unlock" ,
								Type::getVoidTy( M.getContext() ),
								Type::getInt8PtrTy( M.getContext() ),
								Type::getInt8PtrTy( M.getContext() ),
								(Type *)0
								));


					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
					params.push_back(pointerToArray(M,c2));
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

struct RmJoin: public ModulePass {

	static char ID;
	RmJoin() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){


				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_join"){
					instr_to_rm.push_back(in);
				}

			}


		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}


		return false;
	}
};


struct ExtractFn: public ModulePass {

	static char ID;
	ExtractFn() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		string seed = "_Z3fn1Pv";

		map<string, set<string> > calls;
		set<Function*> all_funcs;

		mod_iterator(M, fun){
			all_funcs.insert(fun);
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				calls[fun->getName().str()].insert( in_c->getCalledFunction()->getName().str() );

			}


		}}}

		set<string> functions;
		set<string> functions2;
		functions.insert(seed);

		while(functions2 != functions ){

			functions2 = functions;
			for( set<string>::iterator it = functions.begin(); it != functions.end(); it++ ){
				string currentfunction = *it;
				set<string> current_calls_to = calls[currentfunction];
				for( set<string>::iterator it2 = current_calls_to.begin(); it2 != current_calls_to.end(); it2++ ){
					functions.insert(*it2);
				}


			}
		}


		for( set<Function*>::iterator it = all_funcs.begin(); it != all_funcs.end(); it++ ){
			Function* fn = *it;
			string fnname = fn->getName().str();

			if(functions.find(fnname) == functions.end()){
				fn->eraseFromParent();
			}
		}
		

		Function* fnseed = M.getFunction(seed);

		Function::arg_iterator arg_begin = fnseed->arg_begin();
		Function::arg_iterator arg_end   = fnseed->arg_end();
		vector<string> argNames;
		vector<const Type*>   argTypes;
		for( Function::arg_iterator it = arg_begin; it != arg_end; it++ ){
			argNames.push_back(it->getName().str());
			const Type* t = it->getType();
			argTypes.push_back(t);
		}

		for ( unsigned int i = 0; i < argNames.size(); i++) {
			string name = argNames[i];
			const Type* type = argTypes[i];
			BasicBlock*  bb_ini = fnseed->begin();
			Instruction* in_ini = bb_ini->begin();

			AllocaInst* ai = new AllocaInst(type, 0, (name+"_aux").c_str(), in_ini );



			fun_iterator(fnseed,bb){
			blk_iterator(bb, in){

				for ( unsigned int k = 0; k < in->getNumOperands(); k++) {

					if( in->getOperand(k)->hasName() && (in->getOperand(k)->getName().str() == name) ){
						LoadInst* ai_ptr = new LoadInst(ai,"",in);
						in->setOperand(k, ai_ptr);
					}
				}
			}}


		}

		fnseed->setName("main");
		

		return false;
	}
};


struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		//{SeparateSync     pass;   pass.runOnModule(M);}
		//{ChangePthreadC   pass;   pass.runOnModule(M);}
		//{ChangeSync       pass;   pass.runOnModule(M);}
		//{RmJoin           pass;   pass.runOnModule(M);}
		{ExtractFn        pass;   pass.runOnModule(M);}

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

char RmJoin::ID = 0;
static RegisterPass<RmJoin> RmJoin( "conc_rmjoin", "remove pthread_join");

char ExtractFn::ID = 0;
static RegisterPass<ExtractFn> ExtractFn( "conc_extractfn", "Extract a function and its dependencies");


