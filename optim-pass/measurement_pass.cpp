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

	void put_operator_names( Module &M ){

		mod_iterator(M, fun){
			fun_iterator(fun,bb){
				blk_iterator(bb, in){

					if( UnaryInstruction::classof(in) ){
						if( !in->getOperand(0)->hasName() )
							in->getOperand(0)->setName("r");
						if( !in->hasName() )
							in->setName("r");
					}

					if( BinaryOperator::classof(in) ){
						if( !in->getOperand(0)->hasName() )
							in->getOperand(0)->setName("r");
						if( !in->getOperand(1)->hasName() )
							in->getOperand(1)->setName("r");
						if( !in->hasName() )
							in->setName("r");
					}

					if( CmpInst::classof(in) ){
						if( !in->getOperand(0)->hasName() )
							in->getOperand(0)->setName("r");
						if( !in->getOperand(1)->hasName() )
							in->getOperand(1)->setName("r");
						if( !in->hasName() )
							in->setName("r");
					}

					if( GetElementPtrInst::classof(in) ){
						if( !in->hasName() )
							in->setName("r");
					}

					if( CallInst::classof(in) ){
						if( !in->hasName() )
							in->setName("r");
					}




				}}}

	}


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

		put_operator_names(M);
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
	string position;
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


	std::vector<const Type*>FuncTy_3_args;
	FuncTy_3_args.push_back(IntegerType::get(mod->getContext(), 32));
	PointerType* PointerTy_5 = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
	PointerType* PointerTy_4 = PointerType::get(PointerTy_5, 0);
	FuncTy_3_args.push_back(PointerTy_4);
	Function* func_main = Function::Create(
			FunctionType::get( IntegerType::get(mod->getContext(), 32), FuncTy_3_args, false),
			GlobalValue::ExternalLinkage,
			"main", mod); 

	std::vector<const Type*>FuncTy_7_args;
	Function* func_vector_int = Function::Create(
			FunctionType::get( IntegerType::get(mod->getContext(), 32), FuncTy_7_args, true),
			GlobalValue::ExternalLinkage,
			"vector_int", mod); // (external, no body)




	// Function: main (func_main)
	{
		Function::arg_iterator args = func_main->arg_begin();

		BasicBlock* label_entry = BasicBlock::Create(mod->getContext(), "entry",func_main,0);
		BasicBlock* label_bb = BasicBlock::Create(mod->getContext(), "bb",func_main,0);
		BasicBlock* label_bb2 = BasicBlock::Create(mod->getContext(), "bb2",func_main,0);

		// Block entry (label_entry)
		BranchInst::Create(label_bb, label_entry);

		// Block bb (label_bb)
		Argument* fwdref_16 = new Argument(IntegerType::get(mod->getContext(), 32));
		PHINode* int32_i_04 = PHINode::Create(IntegerType::get(mod->getContext(), 32), "index", label_bb);
		int32_i_04->reserveOperandSpace(2);
		ConstantInt* const_int32_10 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
		int32_i_04->addIncoming(const_int32_10, label_entry);
		int32_i_04->addIncoming(fwdref_16, label_bb);




		for( vector<FreeVariable>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){


			GlobalVariable* gvar_int32_global_int_a = new GlobalVariable(/*Module=*/*mod, 
					IntegerType::get(mod->getContext(), 32),
					false,
					GlobalValue::CommonLinkage,
					0, // has initializer, specified below
					//it->name);
					it->position);
			ConstantInt* const_int32_10 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
			gvar_int32_global_int_a->setInitializer(const_int32_10);

			Constant* const_array_9 = ConstantArray::get(mod->getContext(), it->name, true);
			std::vector<Constant*> const_ptr_11_indices;
			const_ptr_11_indices.push_back(ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
			const_ptr_11_indices.push_back(ConstantInt::get(mod->getContext(), APInt(64, StringRef("1"), 10)));
			GlobalVariable* gvar_array__str = new GlobalVariable(*mod,ArrayType::get(IntegerType::get(mod->getContext(), 8), it->name.length() + 1), true, GlobalValue::PrivateLinkage, 0, "global_" + it->name);
			gvar_array__str->setInitializer(const_array_9);
			CallInst* int32_17 = CallInst::Create(func_vector_int,ConstantExpr::getGetElementPtr(gvar_array__str, &const_ptr_11_indices[0], const_ptr_11_indices.size()), "", label_bb);






			new StoreInst(int32_17, gvar_int32_global_int_a, false, label_bb);


		}

			CallInst* int32_19 = CallInst::Create(func_test, "", label_bb);


		BinaryOperator* int32_20 = BinaryOperator::Create(Instruction::Add, int32_i_04, ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"), 10)), "", label_bb);
		ConstantInt* const_int32_14 = ConstantInt::get(mod->getContext(), APInt(32, StringRef(number_of_times), 10));
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
		string position = tokens[2];
		FreeVariable frv = {name,type, position};
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


map<string, string> load_names_from_pos(){

	map<string, string> ret;

	FILE *file = fopen ( "free_variables", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;


		vector<string> tokens = tokenize(string(line), " ");

		vector<string> tokens2 = tokenize(tokens[2], "_");

		string position;

		if(tokens2[0] == "main")
			position = "test_" + tokens2[2];
		else
			position = tokens2[0] + "_" + tokens2[2];


		string name = tokens[0];

		ret[position] = name;

	}
	fclose ( file );


	for( map<string, string>::iterator it = ret.begin(); it != ret.end(); it++ ){
		cerr << "load_names_from_pos " << it->first << " " << it->second<< endl;
	}
	


	return ret;

}


struct ChangeAssigns: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	ChangeAssigns() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {


		map<string, string> names_from_position = load_names_from_pos();
		
		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){

					string actual_reg_name = fn->getName().str() + "_" + in->getName().str();

					cerr << "actual_reg_name " << actual_reg_name << endl;

					if( names_from_position[actual_reg_name] != "" ){


						//GlobalVariable* gvar_int32_global_a = new GlobalVariable(M, 
								//IntegerType::get(M.getContext(), 32),
								//false,
								//GlobalValue::CommonLinkage,
								//0,
								//"global_a");
						//ConstantInt* const_int32_4 = ConstantInt::get(M.getContext(), APInt(32, StringRef("0"), 10));
						//gvar_int32_global_a->setInitializer(const_int32_4);
						string tgtfnname = (fn->getName().str() == "test")?"main":fn->getName().str();
						GlobalVariable* gvar_int32_global_a = M.getGlobalVariable( tgtfnname+ "_register_" + in->getName().str() );


						BasicBlock::iterator insertpos = in; insertpos++;

						//in->dump();
						new LoadInst(gvar_int32_global_a, "", false, insertpos);

					}

					//in->dump();

				}
			}
		}

		return false;
	}
};




struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		//{BeginEnd      pass;   pass.runOnModule(M);}
		//{BbMarks       pass;   pass.runOnModule(M);}
		{ChangeMain    pass;   pass.runOnModule(M);}
		{ChangeAssigns  pass;   pass.runOnModule(M);}

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

char ChangeAssigns::ID = 0;
static RegisterPass<ChangeAssigns> ChangeAssigns(       "changeassigns"           , "Instrument all operations" );

