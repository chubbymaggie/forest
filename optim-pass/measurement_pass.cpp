/*
 * =====================================================================================
 * /
 * |     Filename:  measurement_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 08:36:01 AM
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
#include <map>

#define mod_iterator(mod, fn) for( Module::iterator     fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define fun_iterator(fun, bb) for( Function::iterator   bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )

using namespace llvm;
using namespace std;


// Helper Functions

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

// Optimization passes

struct FillNames : public ModulePass {

	void put_block_names( Module &M ){

		mod_iterator(M, fun){
			fun_iterator(fun,bb){
				if( !bb->hasName() )
					bb->setName("b");
			} }


	}

	static char ID;
	FillNames() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		put_block_names(M);

		return false;
	}
};

struct BbMarks: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	BbMarks() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){

				string namebb = bb->getName();
				GlobalVariable* c1 = make_global_str(M,namebb);

				Value* InitFn = cast<Value> ( M.getOrInsertFunction( "begin_bb" ,
							Type::getVoidTy( M.getContext() ),
							Type::getInt8PtrTy( M.getContext() ),
							(Type *)0
							));

				Value* EndFn = cast<Value> ( M.getOrInsertFunction( "end_bb" ,
							Type::getVoidTy( M.getContext() ),
							Type::getInt8PtrTy( M.getContext() ),
							(Type *)0
							));

				{
					BasicBlock::iterator insertpos = bb->begin();
					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
					CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
				}

				{
					BasicBlock::iterator insertpos = bb->end(); insertpos--;
					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
					CallInst::Create(EndFn, params.begin(), params.end(), "", insertpos);
				}
			}
		}

		mod_iterator(M, fn){

			string fn_name = fn->getName().str();

			GlobalVariable* c1 = make_global_str(M, fn_name );

			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "BeginFn" ,
						Type::getVoidTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						(Type *)0
						));

			Function::iterator begin = fn->begin();
			Function::iterator end   = fn->end();

			//cerr << "\e[31m" << fn_name << "\e[0m" << endl;
			if( begin != end ){
				//begin->dump();

				BasicBlock::iterator insertpos = fn->begin()->begin();
				//insertpos++;

				std::vector<Value*> params;
				params.push_back(pointerToArray(M,c1));
				CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
				
			}



		}

		return false;

	}
};

struct BeginEnd: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	BeginEnd() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		{
			BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();
	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "begin_sim" ,
						Type::getVoidTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
		}

		{
			Function::iterator insertpos_f = M.getFunction("main")->end();
			insertpos_f--;
			BasicBlock::iterator insertpos_b = insertpos_f->end();
			insertpos_b--;

	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "end_sim" ,
						Type::getVoidTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos_b);
		}

		return false;
	}
};

struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		{BbMarks       pass;   pass.runOnModule(M);}
		{BeginEnd      pass;   pass.runOnModule(M);}

		return false;
	}
};

// Identifiers

char FillNames::ID = 0;
static RegisterPass<FillNames> FillNames(         "meas_fillnames"       , "Instrument Basic-Blocks" );

char BbMarks::ID = 0;
static RegisterPass<BbMarks> BbMarks(             "meas_bbmarks"       , "Instrument Basic-Blocks" );

char BeginEnd::ID = 0;
static RegisterPass<BeginEnd> BeginEnd(           "meas_beginend"      , "Instrument begin and end of program" );

char All::ID = 0;
static RegisterPass<All> All(                     "meas_all"           , "Instrument all operations" );

