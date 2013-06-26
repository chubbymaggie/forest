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

		string functions;
		string basic_blocks;

		mod_iterator(M, fn){
			functions += fn->getName().str() + ",";

			fun_iterator(fn,bb){
				basic_blocks += fn->getName().str() + "_" + bb->getName().str() + ",";
			}
		}

		{

			GlobalVariable* c1 = make_global_str(M,functions);
			GlobalVariable* c2 = make_global_str(M,basic_blocks);

			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "begin_sim" ,
						Type::getVoidTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						(Type *)0
						));


			BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();
			std::vector<Value*> params;
			params.push_back(pointerToArray(M,c1));
			params.push_back(pointerToArray(M,c2));
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


void insert_main_function_calling(Value* fn, Module& M){

	Module* mod = &M;


	// Type Definitions
	std::vector<const Type*>FuncTy_0_args;
	FuncTy_0_args.push_back(IntegerType::get(mod->getContext(), 32));
	PointerType* PointerTy_2 = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);

	PointerType* PointerTy_1 = PointerType::get(PointerTy_2, 0);

	FuncTy_0_args.push_back(PointerTy_1);
	FunctionType* FuncTy_0 = FunctionType::get(
			/*Result=*/IntegerType::get(mod->getContext(), 32),
			/*Params=*/FuncTy_0_args,
			/*isVarArg=*/false);

	PointerType* PointerTy_3 = PointerType::get(IntegerType::get(mod->getContext(), 32), 0);

	PointerType* PointerTy_4 = PointerType::get(PointerTy_1, 0);

	std::vector<const Type*>FuncTy_6_args;
	FunctionType* FuncTy_6 = FunctionType::get(
			/*Result=*/IntegerType::get(mod->getContext(), 32),
			/*Params=*/FuncTy_6_args,
			/*isVarArg=*/true);

	PointerType* PointerTy_5 = PointerType::get(FuncTy_6, 0);


	// Function Declarations

	Function* func_main = Function::Create(
			/*Type=*/FuncTy_0,
			/*Linkage=*/GlobalValue::ExternalLinkage,
			/*Name=*/"main", mod); 
	func_main->setCallingConv(CallingConv::C);
	AttrListPtr func_main_PAL;
	{
		SmallVector<AttributeWithIndex, 4> Attrs;
		AttributeWithIndex PAWI;
		PAWI.Index = 4294967295U; PAWI.Attrs = 0  | Attribute::NoUnwind;
		Attrs.push_back(PAWI);
		func_main_PAL = AttrListPtr::get(Attrs.begin(), Attrs.end());

	}
	func_main->setAttributes(func_main_PAL);

	Function* func_test = cast<Function>(fn);

	func_test->setCallingConv(CallingConv::C);
	AttrListPtr func_test_PAL;
	func_test->setAttributes(func_test_PAL);

	// Global Variable Declarations


	// Constant Definitions
	ConstantInt* const_int32_7 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"), 10));
	ConstantInt* const_int32_8 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));

	// Global Variable Definitions

	// Function Definitions

	// Function: main (func_main)
	{
		Function::arg_iterator args = func_main->arg_begin();
		Value* int32_argc = args++;
		int32_argc->setName("argc");
		Value* ptr_argv = args++;
		ptr_argv->setName("argv");

		BasicBlock* label_entry = BasicBlock::Create(mod->getContext(), "entry",func_main,0);
		BasicBlock* label_return = BasicBlock::Create(mod->getContext(), "return",func_main,0);

		// Block entry (label_entry)
		AllocaInst* ptr_argc_addr = new AllocaInst(IntegerType::get(mod->getContext(), 32), "argc_addr", label_entry);
		ptr_argc_addr->setAlignment(4);
		AllocaInst* ptr_argv_addr = new AllocaInst(PointerTy_1, "argv_addr", label_entry);
		ptr_argv_addr->setAlignment(8);
		AllocaInst* ptr_retval = new AllocaInst(IntegerType::get(mod->getContext(), 32), "retval", label_entry);
		AllocaInst* ptr_9 = new AllocaInst(IntegerType::get(mod->getContext(), 32), "", label_entry);
		CastInst* int32_alloca_point = new BitCastInst(const_int32_8, IntegerType::get(mod->getContext(), 32), "alloca point", label_entry);
		new StoreInst(int32_argc, ptr_argc_addr, false, label_entry);
		new StoreInst(ptr_argv, ptr_argv_addr, false, label_entry);
		CallInst* int32_12 = CallInst::Create(func_test, "", label_entry);
		int32_12->setCallingConv(CallingConv::C);
		int32_12->setTailCall(false);
		AttrListPtr int32_12_PAL;
		{
			SmallVector<AttributeWithIndex, 4> Attrs;
			AttributeWithIndex PAWI;
			PAWI.Index = 4294967295U; PAWI.Attrs = 0  | Attribute::NoUnwind;
			Attrs.push_back(PAWI);
			int32_12_PAL = AttrListPtr::get(Attrs.begin(), Attrs.end());

		}
		int32_12->setAttributes(int32_12_PAL);

		new StoreInst(const_int32_8, ptr_9, false, label_entry);
		LoadInst* int32_14 = new LoadInst(ptr_9, "", false, label_entry);
		new StoreInst(int32_14, ptr_retval, false, label_entry);
		BranchInst::Create(label_return, label_entry);

		// Block return (label_return)
		LoadInst* int32_retval1 = new LoadInst(ptr_retval, "retval1", false, label_return);
		ReturnInst::Create(mod->getContext(), int32_retval1, label_return);

	}
}

vector<string> tokenize(const string& str,const string& delimiters) {
	vector<string> tokens;
    	
	// skip delimiters at beginning.
    	string::size_type lastPos = str.find_first_not_of(delimiters, 0);
    	
	// find first "non-delimiter".
    	string::size_type pos = str.find_first_of(delimiters, lastPos);

    	while (string::npos != pos || string::npos != lastPos)
    	{
		// found a token, add it to the vector.
		tokens.push_back(str.substr(lastPos, pos - lastPos));
	
		// skip delimiters.  Note the "not_of"
		lastPos = str.find_first_not_of(delimiters, pos);
	
		// find next "non-delimiter"
		pos = str.find_first_of(delimiters, lastPos);
    	}

	return tokens;
}

void insert_global_variables(Module& M){

	FILE *file = fopen ( "free_variables", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	vector<string> file_vector;
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		file_vector.push_back(line);
	}
	fclose ( file );

	Module* mod = &M;

	for( vector<string>::iterator it = file_vector.begin(); it != file_vector.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		if( tokens[1] == "Int" ){

			GlobalVariable* gvar_int32_entero = new GlobalVariable(/*Module=*/*mod, 
					/*Type=*/IntegerType::get(mod->getContext(), 32),
					/*isConstant=*/false,
					/*Linkage=*/GlobalValue::CommonLinkage,
					/*Initializer=*/0, // has initializer, specified below
					/*Name=*/"var_global_" + tokens[0]);
			ConstantInt* const_int32_3 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
			gvar_int32_entero->setInitializer(const_int32_3);

		}

		if( tokens[1] == "Float" ){

			GlobalVariable* gvar_float_real = new GlobalVariable(/*Module=*/*mod, 
					/*Type=*/Type::getFloatTy(mod->getContext()),
					/*isConstant=*/false,
					/*Linkage=*/GlobalValue::CommonLinkage,
					/*Initializer=*/0, // has initializer, specified below
					/*Name=*/"var_global_" + tokens[0]);
			ConstantFP* const_float_4 = ConstantFP::get(mod->getContext(), APFloat(0.000000e+00f));
			gvar_float_real->setInitializer(const_float_4);
		}

		if(tokens[1] == "Char"){
			GlobalVariable* gvar_int8_caracter = new GlobalVariable(/*Module=*/*mod, 
					/*Type=*/IntegerType::get(mod->getContext(), 8),
					/*isConstant=*/false,
					/*Linkage=*/GlobalValue::CommonLinkage,
					/*Initializer=*/0, // has initializer, specified below
					/*Name=*/"var_global_" + tokens[0]);
			ConstantInt* const_int8_5 = ConstantInt::get(mod->getContext(), APInt(8, StringRef("0"), 10));
			gvar_int8_caracter->setInitializer(const_int8_5);

		}


	}


}




struct ChangeMain: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	ChangeMain() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		M.getFunction("main")->setName("test");

		Value* InitFn = cast<Value> ( M.getFunction( "test" ));


		insert_main_function_calling(InitFn, M);
		insert_global_variables(M);


		return false;
	}
};

struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		{BeginEnd      pass;   pass.runOnModule(M);}
		{BbMarks       pass;   pass.runOnModule(M);}
		{ChangeMain    pass;   pass.runOnModule(M);}

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

char ChangeMain::ID = 0;
static RegisterPass<ChangeMain> ChangeMain(       "changemain"           , "Instrument all operations" );
