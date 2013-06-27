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



typedef struct FreeVariable{
	string name;
	string type;
} FreeVariable;


//int global_int_a;
//int test(int argc, const char* argv[]);
//int main(int argc, const char *argv[]) {
	//int i;
	//for ( i = 0; i < 5000; i++) {
		//global_int_a = vector_int("a");
		//test( argc, argv );
	//}
	//return 0;
//}
void insert_main_function_calling(Value* func_test, Module* mod, vector<FreeVariable> free_variables, set<vector<string> > values ){

	stringstream number_of_times_ss; number_of_times_ss << values.size();
	string number_of_times = number_of_times_ss.str();


	// Type Definitions
	ArrayType* ArrayTy_0 = ArrayType::get(IntegerType::get(mod->getContext(), 8), 2);

	PointerType* PointerTy_1 = PointerType::get(ArrayTy_0, 0);

	PointerType* PointerTy_2 = PointerType::get(IntegerType::get(mod->getContext(), 32), 0);

	std::vector<const Type*>FuncTy_3_args;
	FuncTy_3_args.push_back(IntegerType::get(mod->getContext(), 32));
	PointerType* PointerTy_5 = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);

	PointerType* PointerTy_4 = PointerType::get(PointerTy_5, 0);

	FuncTy_3_args.push_back(PointerTy_4);
	FunctionType* FuncTy_3 = FunctionType::get(
			/*Result=*/IntegerType::get(mod->getContext(), 32),
			/*Params=*/FuncTy_3_args,
			/*isVarArg=*/false);

	std::vector<const Type*>FuncTy_7_args;
	FunctionType* FuncTy_7 = FunctionType::get(
			/*Result=*/IntegerType::get(mod->getContext(), 32),
			/*Params=*/FuncTy_7_args,
			/*isVarArg=*/true);

	PointerType* PointerTy_6 = PointerType::get(FuncTy_7, 0);

	PointerType* PointerTy_8 = PointerType::get(FuncTy_3, 0);


	// Function Declarations

	Function* func_main = Function::Create(
			/*Type=*/FuncTy_3,
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

	Function* func_vector_int = Function::Create(
			/*Type=*/FuncTy_7,
			/*Linkage=*/GlobalValue::ExternalLinkage,
			/*Name=*/"vector_int", mod); // (external, no body)
	func_vector_int->setCallingConv(CallingConv::C);
	AttrListPtr func_vector_int_PAL;
	func_vector_int->setAttributes(func_vector_int_PAL);

	//Function* func_test = Function::Create(
			//FuncTy_3,
			//GlobalValue::ExternalLinkage,
			//"test", mod); // (external, no body)
	//func_test->setCallingConv(CallingConv::C);
	//AttrListPtr func_test_PAL;
	//func_test->setAttributes(func_test_PAL);

	// Global Variable Declarations


	GlobalVariable* gvar_array__str = new GlobalVariable(/*Module=*/*mod, 
			/*Type=*/ArrayTy_0,
			/*isConstant=*/true,
			/*Linkage=*/GlobalValue::PrivateLinkage,
			/*Initializer=*/0, // has initializer, specified below
			/*Name=*/".str");
	gvar_array__str->setAlignment(1);







	// Constant Definitions
	Constant* const_array_9 = ConstantArray::get(mod->getContext(), "a", true);
	std::vector<Constant*> const_ptr_11_indices;
	ConstantInt* const_int64_12 = ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10));
	ConstantInt* const_int32_10 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
	const_ptr_11_indices.push_back(const_int64_12);
	const_ptr_11_indices.push_back(const_int64_12);
	Constant* const_ptr_11 = ConstantExpr::getGetElementPtr(gvar_array__str, &const_ptr_11_indices[0], const_ptr_11_indices.size());
	ConstantInt* const_int32_13 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"), 10));
	ConstantInt* const_int32_14 = ConstantInt::get(mod->getContext(), APInt(32, StringRef(number_of_times), 10));

	// Global Variable Definitions
	gvar_array__str->setInitializer(const_array_9);

	// Function Definitions

	// Function: main (func_main)
	{
		Function::arg_iterator args = func_main->arg_begin();
		Value* int32_argc = args++;
		int32_argc->setName("argc");
		Value* ptr_argv = args++;
		ptr_argv->setName("argv");

		BasicBlock* label_entry = BasicBlock::Create(mod->getContext(), "entry",func_main,0);
		BasicBlock* label_bb = BasicBlock::Create(mod->getContext(), "bb",func_main,0);
		BasicBlock* label_bb2 = BasicBlock::Create(mod->getContext(), "bb2",func_main,0);

		// Block entry (label_entry)
		BranchInst::Create(label_bb, label_entry);

		// Block bb (label_bb)
		Argument* fwdref_16 = new Argument(IntegerType::get(mod->getContext(), 32));
		PHINode* int32_i_04 = PHINode::Create(IntegerType::get(mod->getContext(), 32), "i.04", label_bb);
		int32_i_04->reserveOperandSpace(2);
		int32_i_04->addIncoming(const_int32_10, label_entry);
		int32_i_04->addIncoming(fwdref_16, label_bb);




	for( vector<FreeVariable>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		
	
		GlobalVariable* gvar_int32_global_int_a = new GlobalVariable(/*Module=*/*mod, 
				/*Type=*/IntegerType::get(mod->getContext(), 32),
				/*isConstant=*/false,
				/*Linkage=*/GlobalValue::CommonLinkage,
				/*Initializer=*/0, // has initializer, specified below
				/*Name=*/it->name);

		ConstantInt* const_int32_10 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
		gvar_int32_global_int_a->setInitializer(const_int32_10);

		CallInst* int32_17 = CallInst::Create(func_vector_int, const_ptr_11, "", label_bb);
		int32_17->setCallingConv(CallingConv::C);
		int32_17->setTailCall(true);
		AttrListPtr int32_17_PAL;
		{
			SmallVector<AttributeWithIndex, 4> Attrs;
			AttributeWithIndex PAWI;
			PAWI.Index = 4294967295U; PAWI.Attrs = 0  | Attribute::NoUnwind;
			Attrs.push_back(PAWI);
			int32_17_PAL = AttrListPtr::get(Attrs.begin(), Attrs.end());

		}
		int32_17->setAttributes(int32_17_PAL);

		new StoreInst(int32_17, gvar_int32_global_int_a, false, label_bb);

		std::vector<Value*> int32_19_params;
		int32_19_params.push_back(int32_argc);
		int32_19_params.push_back(ptr_argv);
		CallInst* int32_19 = CallInst::Create(func_test, int32_19_params.begin(), int32_19_params.end(), "", label_bb);
		int32_19->setCallingConv(CallingConv::C);
		int32_19->setTailCall(true);
		AttrListPtr int32_19_PAL;
		{
			SmallVector<AttributeWithIndex, 4> Attrs;
			AttributeWithIndex PAWI;
			PAWI.Index = 4294967295U; PAWI.Attrs = 0  | Attribute::NoUnwind;
			Attrs.push_back(PAWI);
			int32_19_PAL = AttrListPtr::get(Attrs.begin(), Attrs.end());

		}
		int32_19->setAttributes(int32_19_PAL);

	}








		BinaryOperator* int32_20 = BinaryOperator::Create(Instruction::Add, int32_i_04, const_int32_13, "", label_bb);
		ICmpInst* int1_exitcond = new ICmpInst(*label_bb, ICmpInst::ICMP_EQ, int32_20, const_int32_14, "exitcond");
		BranchInst::Create(label_bb2, label_bb, int1_exitcond, label_bb);

		// Block bb2 (label_bb2)
		ReturnInst::Create(mod->getContext(), const_int32_10, label_bb2);

		// Resolve Forward References
		fwdref_16->replaceAllUsesWith(int32_20); delete fwdref_16;

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


vector<FreeVariable> load_variables(){

	vector<FreeVariable> ret;

	FILE *file = fopen ( "free_variables", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	

	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;

		vector<string> tokens = tokenize(string(line), " ");
		string name = tokens[0];
		string type = tokens[1];
		FreeVariable frv = {name,type};
		ret.push_back(frv);
	}
	fclose ( file );


	//for( vector<FreeVariable>::iterator it = ret.begin(); it != ret.end(); it++ ){
		//cerr << it->name << " " << it->type << endl;
	//}
	

	return ret;

}

set<vector<string> > load_values(){


	set<vector<string> > ret;

	FILE *file = fopen ( "vectors", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;

		vector<string> tokens = tokenize(string(line), " ");

		ret.insert(tokens);

	}
	fclose ( file );
	

	return ret;



}

struct ChangeMain: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	ChangeMain() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		M.getFunction("main")->setName("test");

		Value* InitFn = cast<Value> ( M.getFunction( "test" ));


		vector<FreeVariable> free_variables = load_variables();
		set<vector<string> > values = load_values();

		insert_main_function_calling(InitFn, &M, free_variables, values);


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
