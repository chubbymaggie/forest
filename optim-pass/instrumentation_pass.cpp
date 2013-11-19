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

// Function declaration

int sizeofstruct(const Type* t);
int get_size( const Type* t );
string get_type_str( const Type* t);
string get_flattened_types(const Type* t);

// Type declarations

typedef struct VarInit {
	string name;
	string type;
	string initialization;
} VarInit;

// Helper Functions

string floatvalue( ConstantFP * CF ){

	stringstream ret_ss;
	ret_ss.setf( std::ios::fixed, std:: ios::floatfield );
	ret_ss.precision(5);

	if( CF->getType()->getTypeID() == 1)
		ret_ss << CF->getValueAPF().convertToFloat();
	else
		ret_ss << CF->getValueAPF().convertToDouble();

	return ret_ss.str();

}

string operandname( Value* operand ){

	if( ConstantInt::classof(operand) ){
		ConstantInt* CI = dyn_cast<ConstantInt>(operand);
		int64_t val = CI->getSExtValue();
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
		return nameop1_ss.str();
	} else if( ConstantFP::classof(operand) ){
		ConstantFP* CF = dyn_cast<ConstantFP>(operand);

		stringstream nameop1_ss;
		nameop1_ss << "constant" UNDERSCORE << floatvalue(CF);

		return nameop1_ss.str();
	} else if ( ConstantPointerNull::classof(operand) ){
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE "0";
		return nameop1_ss.str();
	} else if(GlobalVariable::classof(operand)){
		return "global" UNDERSCORE + operand->getName().str();
	} else if(Function::classof(operand)){
		string name = operand->getName();
		if(name.substr(0,1) == "_") name = name.substr(1);
		return "function" UNDERSCORE + name;
	} else {
		return "register" UNDERSCORE + operand->getName().str();
	}

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

string get_flattened_types(const Type* t){
	//t->dump();

	string ret;
	const StructType* t_struct = dyn_cast<StructType>(t);
	const ArrayType*  t_array  = dyn_cast<ArrayType>(t);
	const SequentialType*  t_sequential  = dyn_cast<SequentialType>(t);

	if(t_struct){
		unsigned int numelems = t_struct->getNumElements();

		for ( unsigned int i = 0; i < numelems; i++) {
			ret += get_flattened_types(t_struct->getElementType(i));
		}

		return ret;
	} else if(t_array){
		unsigned int numelems = t_array->getNumElements();

		for ( unsigned int i = 0; i < numelems; i++) {
			ret += get_flattened_types(t_sequential->getElementType());
		}

		return ret;
		
		
	} else {
		return get_type_str(t) + ",";
	}


}

string get_type_str( const Type* t){

	int typId = t->getTypeID();

	//t->dump();
	//cerr << typId << endl;


	if(typId == 1){
		stringstream name;
		name << "FloatTyID";
		return name.str();
	}

	if(typId == 2){
		stringstream name;
		name << "DoubleTyID";
		return name.str();
	}


	if(typId == 9){
		stringstream name;
		name << "IntegerTyID" << t->getPrimitiveSizeInBits();
		return name.str();
	}

	if(typId == 13){
		return "PointerTyID";
	}

	if(typId == 12){
		return "ArrayTyID";
	}

	if(typId == 0){
		return "VoidTyID";
	}

	if(typId == 11){
		return "StructTyID";
		
		////cerr << "typid 11:";
		////t->dump();
		//const StructType* t_s = cast<StructType>(t);
		//return get_flattened_types(t_s);
		

	}

	t->dump();
	cerr << typId << endl;

	assert(0 && "Unknown Type");

}

string get_op_name_from_id(int opId){

	//cerr << "opID " << opId << endl;

	switch(opId){

		case  8: return "+";
		case  9: return "+";
		case 10: return "-";
		case 11: return "-";
		case 12: return "*";
		case 14: return "/";
		case 13: return "*";
		case 15: return "/";
		case 16: return "/";
		case 18: return "%";
		case 19: return "%";
		case 20: return "L";
		case 21: return "R";
		case 22: return "R";
		case 23: return "Y";
		case 24: return "O";
		case 25: return "X";
		default: assert(0 && "Unknown operand");

	}

}

vector<string> get_indexes(GetElementPtrInst* instr){

	vector<string> ret;
	User::op_iterator it_begin = instr->idx_begin();
	User::op_iterator it_end   = instr->idx_end();

	for( User::op_iterator it = it_begin; it != it_end; it++){

		ConstantInt* CI = dyn_cast<ConstantInt>(it->get());
		if(CI){
			int64_t val = CI->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
			ret.push_back( nameop1_ss.str() );
		} else {
			Value* value = it->get();
			string name = value->getName().str();
			stringstream nameop1_ss; nameop1_ss << "register" UNDERSCORE << name;
			ret.push_back( nameop1_ss.str() );


		}
	}

	return ret;

}


vector<int> get_indexes_gepop(GEPOperator* gepop){

	vector<int> ret;
	User::op_iterator it_begin = gepop->idx_begin();
	User::op_iterator it_end   = gepop->idx_end();

	for( User::op_iterator it = it_begin; it != it_end; it++){

		ConstantInt* CI = dyn_cast<ConstantInt>(it->get());
		if(CI){
			int64_t val = CI->getSExtValue();
			ret.push_back(val);
		} else {

			assert(0 && "non-constant index in gepop");

		}
	}

	return ret;

}


int primary_size( const Type* t ){

	//cerr << "primary_size: " << endl;
	//t->dump();
	//cerr << t->getTypeID() << endl;
	//cerr << t->getPrimitiveSizeInBits() << endl;
	//cerr << "---------" << endl;

	string type = get_type_str(t);

	if( type == "IntegerTyID32" ) return 4;
	if( type == "IntegerTyID16" ) return 2;
	if( type == "IntegerTyID8" ) return 1;
	if( type == "IntegerTyID64" ) return 8;
	if( type == "PointerTyID" ) return 4;
	if( type == "FloatTyID" ) return 8;
	if( type == "DoubleTyID" ) return 8;

	cerr << type << endl;
	assert(0 && "Unknown type");

}

vector<int> get_dimensions( const ArrayType* t ){

		vector<int> dims;
		while(true){
			if( !t ) break;
			dims.push_back(t->getNumElements());
			t = dyn_cast<ArrayType>(t->getElementType());

		};

		return dims;
}

int element_size( const ArrayType* t ){

	const Type* last_type;

	while(true){
		if( !t ) break;
		last_type = t;
		t = dyn_cast<ArrayType>(t->getElementType());
	};

	last_type = dyn_cast<ArrayType>(last_type)->getElementType();

	//return primary_size( last_type );

	const StructType* t_s = dyn_cast<StructType>(last_type);

	if (t_s){
		return sizeofstruct(last_type);
	} else {
		return primary_size(last_type);
	}

}

const Type* element_type( const ArrayType* t ){

	const Type* last_type;

	while(true){
		if( !t ) break;
		last_type = t;
		t = dyn_cast<ArrayType>(t->getElementType());
	};

	last_type = dyn_cast<ArrayType>(last_type)->getElementType();

	return last_type;

}

int product(vector<int> elem){
	int prod = 1;
	for( vector<int>::iterator it = elem.begin(); it != elem.end(); it++ ){
		prod *= *it;
	}
	return prod;
}

int sizeofstruct(const Type* t){

	int ret = 0;
	const StructType* t_s = dyn_cast<StructType>(t);

	unsigned int numelems = t_s->getNumElements();

	for ( unsigned int i = 0; i < numelems; i++) {
		ret += get_size( t_s->getElementType(i) );
	}

	//return t_s->getNumElements();
	return ret;
}

int get_size( const Type* t ){

	const ArrayType* t_a = dyn_cast<ArrayType>(t);
	const StructType* t_s = dyn_cast<StructType>(t);


	if( t_a ){
		return product(get_dimensions(t_a))*element_size(t_a);
	} else if (t_s){
		return sizeofstruct(t);
	} else {
		return primary_size(t);
	}

}

vector<string> get_nested_sizes( const ArrayType* t ){

	//const PointerType* t_p = dyn_cast<PointerType>(t);
	//t = dyn_cast<ArrayType>(t_p->getElementType());

	vector<int> ret;

	const ArrayType* t_ini = t;

	//const ArrayType* t_a = dyn_cast<ArrayType>(t);
	//if( !t_a ){ ret.push_back(1); return ret; }

	//t->dump(); fflush(stderr);
	//cerr << "nestedsizes" << t << endl; fflush(stderr);

	ret.push_back( t->getNumElements() * get_size(t->getElementType()) );

	//cerr << "nestedsizes2" << endl; fflush(stderr);


	while(true){
		t = dyn_cast<ArrayType>(t->getElementType());
		if( !t ) break;
		ret.push_back( t->getNumElements() * get_size(t->getElementType()) );
	};

	ret.push_back( element_size(t_ini) );


	vector<string> ret2;// ret2.push_back("0");
	for( vector<int>::iterator it = ret.begin(); it != ret.end(); it++ ){
		stringstream ss;
		ss << "constant" UNDERSCORE;
		ss << *it;
		ret2.push_back(ss.str());
	}
	


	return ret2;


}

vector<string> get_struct_offsets( const StructType* t ){

	vector<string> ret;

	unsigned int numelems = t->getNumElements();

	int offset = 0;

	for ( unsigned int i = 0; i < numelems; i++) {
		stringstream ss;
		ss << "constant" UNDERSCORE;
		ss << offset;
		ret.push_back(ss.str());

		offset += get_size( t->getElementType(i) );
	}

	return ret;

}

void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

string itos( int value ){
	stringstream ret_ss;
	ret_ss << value;
	return ret_ss.str();
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


int get_offset(const Type* t, int debug = 1){

	//cerr << "get_offset "; t->dump();
	const PointerType*      t_pointer      = dyn_cast<PointerType>(t);
	const StructType*       t_struct       = dyn_cast<StructType>(t);
	const ArrayType*        t_array        = dyn_cast<ArrayType>(t);
	const SequentialType*   t_sequential   = dyn_cast<SequentialType>(t);
	const IntegerType*      t_integer      = dyn_cast<IntegerType>(t);
	const CompositeType*    t_composite    = dyn_cast<CompositeType>(t);

	string type_str = get_type_str(t);

	if(type_str == "PointerTyID"){
		//cerr << "pointer " << endl;
		return get_offset(t_pointer->getElementType());
	} else if( type_str == "StructTyID"){
		return -1;
	} else if(type_str == "ArrayTyID"){
		//cerr << "array " << endl;

		int sum = 0;
		for ( unsigned int i = 0; i < t_array->getNumElements(); i++) {
			sum += get_offset(t_composite->getTypeAtIndex(i));
		}

		return sum;
	} else if( type_str == "IntegerTyID"){

		//cerr << "Integer" << endl;

		return get_size(t);

	} else if( type_str == "IntegerTyID32"){
		//cerr << "Integer32" << endl;

		return get_size(t);

	} else if( type_str == "IntegerTyID8"){
		//cerr << "Integer8" << endl;

		return get_size(t);

	} else if (type_str == "DoubleTyID"){
		//cerr << "double" << endl;

		return get_size(t);

	} else if (type_str == "FloatTyID"){
		//cerr << "float" << endl;

		return get_size(t);

	} else {

		//cerr << "----" << endl;
		//cerr << "otro" << endl;
		//t->dump();
		//cerr << type_str << endl;
		assert(0 && "Unknown Type");

	}

}


string get_offset_tree( const Type* t, int* base){

	const PointerType*      t_pointer      = dyn_cast<PointerType>(t);
	const StructType*       t_struct       = dyn_cast<StructType>(t);
	const ArrayType*        t_array        = dyn_cast<ArrayType>(t);
	const SequentialType*   t_sequential   = dyn_cast<SequentialType>(t);
	const IntegerType*      t_integer      = dyn_cast<IntegerType>(t);
	const CompositeType*    t_composite    = dyn_cast<CompositeType>(t);

	string type_str = get_type_str(t);

	if(type_str == "PointerTyID"){
		//cerr << "pointer" << endl;

		return "(" + get_offset_tree(t_sequential->getElementType(), base) + "," + itos(get_offset(t)) + ")";

	//} else if(type_str.find(",") != string::npos ){
	} else if( type_str == "StructTyID"){

		//cerr << "struct" << endl;

		string aux = "(";
		for ( unsigned int i = 0; i < t_struct->getNumElements(); i++) {
			//cerr << "element " << i << endl;
			aux += get_offset_tree(t_struct->getElementType(i),base);
		}
		aux += "," + itos(get_offset(t));
		aux += ")";
		return aux;

	} else if(type_str == "ArrayTyID"){

		//cerr << "array" << endl;
		//t->dump();

		string aux = "(";
		for ( unsigned int i = 0; i < t_array->getNumElements(); i++) {
			aux += get_offset_tree(t_composite->getTypeAtIndex(i),base);
		}
		aux += "," + itos(get_offset(t));
		aux += ")";
		return aux;


	} else if( type_str == "IntegerTyID"){

		//cerr << "integer " << primary_size(t) << endl;
		return itos( primary_size(t) ) + " ";

	} else if( type_str == "IntegerTyID32"){

		//cerr << "integer32 " << primary_size(t) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(t);
		return ret;

	} else if( type_str == "IntegerTyID8"){

		//cerr << "integer8 " << primary_size(t) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(t);
		return ret;

	} else if (type_str == "DoubleTyID"){

		//cerr << "double " << primary_size(t) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(t);
		return ret;

	} else if (type_str == "FloatTyID"){

		//cerr << "float " << primary_size(t) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(t);
		return ret;

	} else {

		//cerr << "----" << endl;
		//cerr << "otro" << endl;
		//t->dump();
		//cerr << type_str << endl;
		assert(0 && "Unknown Type");

	}
}



// Optimization passes

struct FillNames : public ModulePass {

	void put_operator_names( Module &M ){


		//mod_iterator(M, fun){
			//fun_iterator(fun,bb){
				//blk_iterator(bb, in){

					//string name = in->getName().str();
					//myReplace(name, "_", "");
					//in->setName(name);


				//}
			//}
		//}

		glo_iterator(M,gl){

			string name = gl->getName().str();
			myReplace(name, "_", "");
			gl->setName(name);

		}



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
							if( !(in->getType()->isVoidTy()) )
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

struct SelectInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	SelectInstr() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( SelectInst::classof(in) ){

						//in->dump();
						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );
						string nameop3 = operandname( in->getOperand(2) );

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, nameop2);
						GlobalVariable* c4 = make_global_str(M, nameop3);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "select_op" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
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
						params.push_back(pointerToArray(M,c4));
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}
				}
			}
		}

		return false;
	}
};

struct BinaryOp: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	BinaryOp() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( BinaryOperator::classof(in) ){

						//in->dump();
						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );
						int nameop     = in->getOpcode();

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, nameop2);
						GlobalVariable* c4 = make_global_str(M, get_op_name_from_id(nameop));


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "binary_op" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
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
						params.push_back(pointerToArray(M,c4));
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

						//CallInst* ci = CallInst::Create(InitFn, "", insertpos );

					}
				}
			}
		}

		return false;
	}
};

struct CastInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	CastInstr() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CastInst::classof(in) ){

						if( in->getName() == "alloca point" ) continue;

						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string type = get_type_str( in->getType() );

						//cerr << nameres << " " << nameop1 << endl;

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, type);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "cast_instruction" ,
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
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);


					}
				}
			}
		}

		return false;
	}
};

struct LoadStore: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	LoadStore() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( LoadInst::classof(in) ){

						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "load_instr" ,
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

					if( StoreInst::classof(in) ){

						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );

						GlobalVariable* c1 = make_global_str(M, nameop1);
						GlobalVariable* c2 = make_global_str(M, nameop2);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "store_instr" ,
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
			}
		}

		return false;
	}
};

struct SeparateGetElm: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	SeparateGetElm() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( LoadInst::classof(in) ){


						bool is_getelement = !(in->getOperand(0)->hasName());

						if( is_getelement ){

							GEPOperator* gepop = dyn_cast<GEPOperator>(in->getOperand(0));
							Value* pointer = gepop->getPointerOperand();
							User::op_iterator idxbegin = gepop->idx_begin();
							User::op_iterator idxend   = gepop->idx_end();
							vector<Value*> indices(idxbegin, idxend);

							GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);

							in->setOperand(0,getelement);

							//gepop->dump();
							//pointer->dump();
							//(*idxbegin)->dump();


						}

					}

					if( StoreInst::classof(in) ){

						for ( unsigned int i = 0; i < 2; i++) {

							bool is_getelement = !(in->getOperand(i)->hasName());
							GEPOperator* gepop = dyn_cast<GEPOperator>(in->getOperand(i));

							if( is_getelement && gepop ){
								//in->dump();


								Value* pointer = gepop->getPointerOperand();
								User::op_iterator idxbegin = gepop->idx_begin();
								User::op_iterator idxend   = gepop->idx_end();
								vector<Value*> indices(idxbegin, idxend);

								GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);

								in->setOperand(i,getelement);


							}
						}

					}

					if( CallInst::classof(in) ){


						CallInst* in_c = cast<CallInst>(in);

						for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {

							bool is_getelement = !(in_c->getArgOperand(i)->hasName());
							GEPOperator* gepop = dyn_cast<GEPOperator>(in_c->getArgOperand(i));


							if( is_getelement && gepop ){

								Value* pointer = gepop->getPointerOperand();
								User::op_iterator idxbegin = gepop->idx_begin();
								User::op_iterator idxend   = gepop->idx_end();
								vector<Value*> indices(idxbegin, idxend);
								GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);
								in->setOperand(i,getelement);

							}

						}

					}

					if( GetElementPtrInst::classof(in) ){

						GetElementPtrInst* in_g = cast<GetElementPtrInst>(in);

						bool is_getelement = !(in_g->getPointerOperand()->hasName());
						GEPOperator* gepop = dyn_cast<GEPOperator>(in_g->getPointerOperand());

						if( is_getelement && gepop ){

							Value* pointer = gepop->getPointerOperand();
							User::op_iterator idxbegin = gepop->idx_begin();
							User::op_iterator idxend   = gepop->idx_end();
							vector<Value*> indices(idxbegin, idxend);
							GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);
							in->setOperand(0,getelement);

						}

					}

				}

			}

		}

		return false;
	}
};

struct IcmpInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	IcmpInstr() : ModulePass(ID) {}

	string get_predicate( CmpInst* instr ){
		switch( instr->getPredicate() ){

			case CmpInst::FCMP_FALSE           : return "";
			case CmpInst::FCMP_OEQ             : return "=";
			case CmpInst::FCMP_OGT             : return ">";
			case CmpInst::FCMP_OGE             : return ">=";
			case CmpInst::FCMP_OLT             : return "<";
			case CmpInst::FCMP_OLE             : return "<=";
			case CmpInst::FCMP_ONE             : return "#";
			case CmpInst::FCMP_ORD             : return "";
			case CmpInst::FCMP_UNO             : return "";
			case CmpInst::FCMP_UEQ             : return "=";
			case CmpInst::FCMP_UGT             : return ">";
			case CmpInst::FCMP_UGE             : return ">=";
			case CmpInst::FCMP_ULT             : return "<";
			case CmpInst::FCMP_ULE             : return "<=";
			case CmpInst::FCMP_UNE             : return "#";
			case CmpInst::FCMP_TRUE            : return "";
			case CmpInst::BAD_FCMP_PREDICATE   : return "";
			case CmpInst::ICMP_EQ              : return "=";
			case CmpInst::ICMP_NE              : return "#";
			case CmpInst::ICMP_UGT             : return ">";
			case CmpInst::ICMP_UGE             : return ">=";
			case CmpInst::ICMP_ULT             : return "<";
			case CmpInst::ICMP_ULE             : return "<=";
			case CmpInst::ICMP_SGT             : return ">";
			case CmpInst::ICMP_SGE             : return ">=";
			case CmpInst::ICMP_SLT             : return "<";
			case CmpInst::ICMP_SLE             : return "<=";
			case CmpInst::BAD_ICMP_PREDICATE   : return "";
			defalut: assert(0 && "Unknown Operation");

		}
	}

	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CmpInst::classof(in) ){

						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );
						string cmptype = get_predicate( cast<CmpInst>(in) );

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, nameop2);
						GlobalVariable* c4 = make_global_str(M, cmptype);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "cmp_instr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
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
						params.push_back(pointerToArray(M,c4));
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}
				}
			}
		}

		return false;
	}
};

struct BrInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	BrInstr() : ModulePass(ID) {}

	vector<string> basic_blocks( Module::iterator fn ){

		vector<string> ret;

		fun_iterator(fn, bb){

			ret.push_back( bb->getName().str() );

		}

		return ret;
	}

	map<string, map<string, bool> > conectivity_matrix( Module::iterator fn ){

		map<string, map<string, bool> > ret;

		vector<string> bbs = basic_blocks( fn );

		for ( unsigned int x = 0; x < bbs.size(); x++) {
			for ( unsigned int y = 0; y < bbs.size(); y++) {
				string src = bbs[x];
				string dst = bbs[y];
				ret[src][dst] = 0;
			}
		}

		fun_iterator(fn, bb){

			BasicBlock::iterator in = bb->end(); in--;

			BranchInst* in_b = dyn_cast<BranchInst>(in);
			if(!in_b) continue;

			for ( unsigned int i = 0; i < in_b->getNumSuccessors(); i++) {
				string src = bb->getName().str();
				string dst = in_b->getSuccessor(i)->getName().str();

				ret[src][dst] = 1;

			}

		}

		return ret;

	}


	set<string> one_pass_reachable(string bb, map<string, map<string, bool> > connectivity, set<string> reachable_set, Module::iterator fn ){


		//cerr << "opr1" << endl; fflush(stderr);
		
		set<string> ret = reachable_set;
		vector<string> bbs = basic_blocks( fn );

		for( set<string>::iterator it = reachable_set.begin(); it != reachable_set.end(); it++ ){

			string src = *it;

			for ( unsigned int i = 0; i < connectivity.size(); i++) {
				string dst = bbs[i];
				if( connectivity[src][dst] ) ret.insert(dst);
			}
		}

		return ret;

	}

	set<string> reachable(string bb, Module::iterator fn ){

		map<string, map<string, bool> > connectivity = conectivity_matrix(fn);

		set<string> reachable_set_last;
		set<string> reachable_set;
		//cerr << "reach1" << endl; fflush(stderr);
		reachable_set.insert(bb);
		//cerr << "reach2" << endl; fflush(stderr);

		while( reachable_set_last != reachable_set ){
			reachable_set_last = reachable_set;
			reachable_set      = one_pass_reachable( bb, connectivity, reachable_set, fn);
		}

		return reachable_set;

	}


	set<string> intersection( set<string> s1, set<string> s2 ){

		set<string> ret;
		for( set<string>::iterator it = s1.begin(); it != s1.end(); it++ ){
			if( s2.find(*it) != s2.end() ) ret.insert(*it);
		}

		return ret;

	}



	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fn){

			map<string, map<string, bool> > conectivity = conectivity_matrix(fn);
			vector<string> bbs = basic_blocks( fn );

			//for( vector<string>::iterator it = bbs.begin(); it != bbs.end(); it++ ){
				//cerr << *it << " ";
			//} cerr << endl;
			

			//for ( unsigned int x = 0; x < bbs.size(); x++) {
				//for ( unsigned int y = 0; y < bbs.size(); y++) {
					//string src = bbs[x];
					//string dst = bbs[y];
					//cerr << conectivity[src][dst];
				//}
				//cerr << endl;
			//}
			//cerr << endl;
			
			//cerr << "\033[32m" << fn->getName().str() << "\033[0m" << endl;

			for ( unsigned int i = 0; i < bbs.size(); i++) {

				string src = bbs[i];

				set<string> reachable_set = reachable( src, fn );

				//cerr << "\033[31m" << src << "\033[0m" << endl;
				//for( set<string>::iterator it = reachable_set.begin(); it != reachable_set.end(); it++ ){
					//cerr << *it << " ";
				//} cerr << endl;

			}
			

			//for( map<string,map<string, bool> >::iterator it = conectivity.begin(); it != conectivity.end(); it++ ){
				//for( map<string,bool>::iterator it2 = it->second.begin(); it2 != it->second.end(); it2++ ){

					//cerr << " " << it2->second << " ";
					
				//}

				//cerr << endl;
				
			//}
			


			fun_iterator(fn, bb){

				blk_iterator(bb, in){
					if( BranchInst::classof(in) ){

						BranchInst* in_b = cast<BranchInst>(in);

						if( in_b->isConditional() ){

							string name1 = in_b->getSuccessor(0)->getName().str();
							string name2 = in_b->getSuccessor(1)->getName().str();
							set<string> reachable_1 = reachable(name1, fn);
							set<string> reachable_2 = reachable(name2, fn);
							set<string> joints = intersection(reachable_1, reachable_2);


							string joints_s;
							for( set<string>::iterator it = joints.begin(); it != joints.end(); it++ ){
								joints_s = joints_s + (*it) + ",";
							}
							

							//cerr << "\033[31m" << joints_s << "\033[0m" << endl;

							string nameop1 = operandname( in->getOperand(0) );

							GlobalVariable* c1 = make_global_str(M, nameop1);
							GlobalVariable* c2 = make_global_str(M, joints_s);

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "br_instr_cond" ,
										Type::getInt1Ty( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in; //insertpos++;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c1));
							params.push_back(pointerToArray(M,c2));

							CallInst* ci = CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
							if( in_b->isConditional() )
								in_b->setCondition(ci);

						} else {

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "br_instr_incond" ,
										Type::getVoidTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in; //insertpos++;

							std::vector<Value*> params;
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

						}
					}
				}
			}
		}

		return false;
	}
};

struct CallInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	CallInstr() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CallInst::classof(in) ){

						//cerr << "Instruction ";
						//in->dump();

						CallInst* in_c = cast<CallInst>(in);

						bool hasname = in_c->getCalledFunction();

						string fn_name;
					        if(hasname)
							fn_name = in_c->getCalledFunction()->getName().str();
						else
							fn_name ="";

						if(fn_name == "global_var_init") continue;


						stringstream operand_list;
						for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {
							string name = operandname( in_c->getArgOperand(i) );
							operand_list << name << ",";
						}


						string oplist  = operand_list.str();
						string ret_to = operandname( in_c );
						string ret_type = get_type_str( in_c->getType() );
						
						//cerr << fn_name << endl;
						//cerr << oplist  << endl;
						//cerr << fn_oplist << endl;


						bool annotated = hasname && ( in_c->getCalledFunction()->begin() != in_c->getCalledFunction()->end() );
						bool freefn = (fn_name == "_Z10force_freePi");
						bool forcepivot = (fn_name == "_Z9pivot_varPi");
						//cerr << "name " << fn_name << endl;
						//cerr << "freefn " << freefn << endl;
						//cerr << "annotated " << annotated << endl;


						if( annotated ){

							GlobalVariable* c1 = make_global_str(M, oplist );
							GlobalVariable* c2 = make_global_str(M, ret_to );

							//void CallInstr( char* _oplist, char* _ret_to );
							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "CallInstr" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c1));
							params.push_back(pointerToArray(M,c2));
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

						} else if(freefn){

							
							GlobalVariable* c2 = make_global_str(M, oplist );

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "Free_fn" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c2));
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
						} else if(forcepivot) {

							GlobalVariable* c2 = make_global_str(M, oplist );

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "pivot_variable" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c2));
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

						} else {
							GlobalVariable* c1 = make_global_str(M, fn_name );
							GlobalVariable* c2 = make_global_str(M, ret_to );
							GlobalVariable* c3 = make_global_str(M, ret_type );

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "NonAnnotatedCallInstr" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c1));
							params.push_back(pointerToArray(M,c2));
							params.push_back(pointerToArray(M,c3));
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

						}
							

					}
				}
			}
		}


		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( ReturnInst::classof(in) ){

						ReturnInst* in_r = cast<ReturnInst>(in);


						string returnoperand;
						if( !in_r->getReturnValue() )
							returnoperand = "register" UNDERSCORE;
						else
							returnoperand = operandname( in_r->getReturnValue() );

						GlobalVariable* c1 = make_global_str(M, returnoperand );

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "ReturnInstr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						BasicBlock::iterator insertpos = in;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);




					}

				}
			}
		}





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


			Function::arg_iterator arg_begin = fn->arg_begin();
			Function::arg_iterator arg_end   = fn->arg_end();

			stringstream function_operand_list;
			for( Function::arg_iterator it = arg_begin; it != arg_end; it++ ){
				function_operand_list << operandname(it) << ",";
			}
			string fn_oplist = function_operand_list.str();

			GlobalVariable* c1 = make_global_str(M, fn_name );
			GlobalVariable* c2 = make_global_str(M, fn_oplist);

			//void BeginFn(char* _fn_name, char* fn_oplist);
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "BeginFn" ,
						Type::getVoidTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
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
				params.push_back(pointerToArray(M,c2));
				CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
				
			}



		}

		return false;

	}
};

struct AllocaInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	AllocaInstr() : ModulePass(ID) {}



	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( AllocaInst::classof(in) ){

						AllocaInst* in_a = cast<AllocaInst>(in);

						string nameres = "register" UNDERSCORE + in->getName().str();

						string type = get_type_str(in_a->getAllocatedType());
						string subtype = get_flattened_types( in_a->getAllocatedType() );

						//cerr << "subtype " << subtype << endl;

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, subtype);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "alloca_instr" ,
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
			}
		}

		return false;
	}
};

struct GetelementPtr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	GetelementPtr() : ModulePass(ID) {}



	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( GetElementPtrInst::classof(in) ){

						GetElementPtrInst* in_g = cast<GetElementPtrInst>(in);
						Value* pointer = in_g->getPointerOperand();


						GlobalVariable* pointer_global = dyn_cast<GlobalVariable>(pointer);

						string nameres = "register" UNDERSCORE + in->getName().str();

						string nameop1;
						if( pointer_global )
							nameop1 = "global" UNDERSCORE + pointer->getName().str();
						else
							nameop1 = "register" UNDERSCORE + pointer->getName().str();

						
						vector<string> indexes = get_indexes(in_g);
						string indexes_str;
						for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
							indexes_str += *it + ",";
						}

						int base = 0;
						string offset_tree = get_offset_tree(in_g->getPointerOperand()->getType(), &base);

						const PointerType* pointertype = cast<PointerType>(in_g->getPointerOperand()->getType());
						const Type*        pointedtype = pointertype->getElementType();
						int   elementsize = get_size(pointedtype);
						string elementsize_s = itos(elementsize);

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, indexes_str);
						GlobalVariable* c4 = make_global_str(M, offset_tree);
						GlobalVariable* c5 = make_global_str(M, elementsize_s);

						Value* InitFn;

						InitFn = cast<Value> ( M.getOrInsertFunction( "getelementptr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
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
						params.push_back(pointerToArray(M,c4));
						params.push_back(pointerToArray(M,c5));
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}
				}
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


struct MainArgs: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	MainArgs() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {


		Function* fn = M.getFunction("main");

		Function::arg_iterator arg_begin = fn->arg_begin();
		Function::arg_iterator arg_end   = fn->arg_end();
		if(arg_begin == arg_end) return false;

		BasicBlock* fnbegin = fn->begin();
		Instruction* inbegin = fnbegin->begin();

		AllocaInst* argc_addr = new AllocaInst(IntegerType::get(M.getContext(), 32), "argc_addr", inbegin );
		
		PointerType* PointerTy_2 = PointerType::get(IntegerType::get(M.getContext(), 8), 0);
		PointerType* PointerTy_1 = PointerType::get(PointerTy_2, 0);
		AllocaInst*  argv_addr   = new AllocaInst(PointerTy_1, "argv_addr", inbegin);


		//ConstantInt* const_int_1 = ConstantInt::get(M.getContext(), APInt(64, StringRef("1"), 10));
		//GetElementPtrInst* argc  = GetElementPtrInst::Create(argc_addr, const_int_1, "argc", inbegin);
		//GetElementPtrInst* argv  = GetElementPtrInst::Create(argv_addr, const_int_1, "argv", inbegin);
		
		LoadInst* argc = new LoadInst(argc_addr, "argc", false, inbegin);
		LoadInst* argv = new LoadInst(argv_addr, "argv", false, inbegin);

		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( StoreInst::classof(in) ){
				string name = in->getOperand(0)->getName().str();
				if(name == "argc"){
					in->setOperand(0, argc);
				}
				if(name == "argv"){
					in->setOperand(0, argv);
				}
			}
		}}

	}

};



struct GlobalInit: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	GlobalInit() : ModulePass(ID) {}

	map<string, int> given_addr;
	int current_addr = 0;


	bool is_number(const std::string& s) {
	
		//printf("\e[33m is_number \e[0m %s\n", s.c_str() );
	
		if( s== "true" || s== "false") return true;
	
		if(s.substr(0,1) == "-") return is_number(s.substr(1));
	
		//printf("%s\n", s.substr(0,s.find(".")).c_str() );
		//printf("%s\n", s.substr(s.find(".")+1).c_str() );
		if( s.find(".") != string::npos ) return 
			is_number(s.substr(0,s.find("."))) &&
			is_number(s.substr(s.find(".")+1));
	
	
		if( s.find("e") != string::npos ) return 
			is_number(s.substr(0,s.find("e"))) &&
			is_number(s.substr(s.find("e")+1));
	
		std::string::const_iterator it = s.begin();
		while (it != s.end() && std::isdigit(*it)) ++it;
		return !s.empty() && it == s.end();
	}


	string close_str(string offset_tree){
	
		int depth = 0;
		for ( unsigned int i = 0; i < offset_tree.size(); i++) {
			if(offset_tree[i] == '(') depth++;
			if(offset_tree[i] == ')') depth--;
			if(depth == 0) return offset_tree.substr(0,i+1);
		}
	
		assert(0 && "Unbalanced tree");
	
	}
	
	string trimpar(string str){
	
		int n1 = str.find_first_not_of("()");
		int n2 = str.substr(n1).find_first_not_of("0123456789-");
		string firstnum = str.substr(n1).substr(0,n2);
		//printf("trimpar %s %s %d %d %s\n", str.c_str(), str.substr(n1).c_str(),  n1, n2, str.substr(n1).substr(0,n2).c_str() );
		assert( is_number(firstnum) && "ret is not a number");
		return firstnum;
	}

	bool has_index(string offset_tree, int index){
	
		int depth = -1;
		int nelem = -1;
		for ( unsigned int i = 1; i < offset_tree.size(); i++) {
			if(offset_tree[i] == '(') depth++;
			if(offset_tree[i] == ')') depth--;
			if(depth == 0 && offset_tree[i] == '(' ){
				nelem++;
			}
			if(nelem == index){
				return true;
	
			}
		}
	
		return false;
	}

	int get_ini_elem(int nelem_target, string offset_tree){
	
		int depth = -1;
		int nelem = -1;
		for ( unsigned int i = 1; i < offset_tree.size(); i++) {
			if(offset_tree[i] == '(') depth++;
			if(offset_tree[i] == ')') depth--;
			if(depth == 0 && offset_tree[i] == '(' ){
				nelem++;
				//printf("elem %d at %d\n", nelem, i);
			}
			if(nelem == nelem_target){
				//printf("get_ini_elem %d %s : %d\n", nelem_target, offset_tree.c_str(), i);
				return i;
	
			}
		}
	
		assert(0 && "Unbalanced tree");
	
	}

	int stoi(string str){
		int ret;
		sscanf(str.c_str(), "%d", &ret);
		return ret;
	}

	int get_offset(vector<int> indexes, string offset_tree){
	
	
		//for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
			//debug && printf("\e[33m %s ", it->c_str() );
		//} debug && printf(" --- ");
		//debug && printf(" offset %s\e[0m\n", offset_tree.c_str() );
		
		int index_0 = indexes[0];
	
		//debug && printf("\e[33m %s %s \e[0m\n", indexes[0].c_str(), realvalue(indexes[0]).c_str() );
	
		//int realvalue_index_0 = stoi(realvalue_index_0_s);
	
		if( has_index(offset_tree, index_0) ){
	
			int ini_elem = get_ini_elem(index_0, offset_tree);
			string right_str = offset_tree.substr(ini_elem);
			string elem_str = close_str(right_str);
			//printf("elem_str %s\n", elem_str.c_str());
	
			vector<int>::iterator first_it = indexes.begin(); first_it++;
			vector<int> rem_indexes = vector<int>(first_it, indexes.end());
	
			if( rem_indexes.size() ){
				return get_offset(rem_indexes, elem_str);
			} else {
				return stoi(trimpar(elem_str));
			}
	
		} else {
			vector<string> tokens = tokenize(offset_tree, "(),");
			string size_s = tokens[tokens.size()-1];
			int size = stoi(size_s);
			//printf("offset_tree %s realvalue_index_0 %d size_s %s\n", offset_tree.c_str(), realvalue_index_0, size_s.c_str());
			return size*index_0;
		}
	
	}




	string get_flattened_vals( Constant* constant ){

		cerr << "get_flattened_vals ";
		constant->dump();

		//cerr << "type" << endl;
		//cerr << ConstantUndefValue::classof(constant) << endl;

		ConstantInt*         constant_int          = dyn_cast<ConstantInt>(constant);
		ConstantArray*       constant_array        = dyn_cast<ConstantArray>(constant);
		ConstantFP*          constant_float        = dyn_cast<ConstantFP>(constant);
		ConstantStruct*      constant_struct       = dyn_cast<ConstantStruct>(constant);
		ConstantPointerNull* constant_pointer_null = dyn_cast<ConstantPointerNull>(constant);
		GlobalValue*         constant_global       = dyn_cast<GlobalValue>(constant);
		GEPOperator*         gepop                 = dyn_cast<GEPOperator>(constant);

		//cerr << "constant_global: ";
		//constant_global->dump();


		string type = get_type_str(constant->getType());

		cerr << "type " << type << endl;
		//if(constant_global)
		//cerr << "name " << constant_global->getName().str() << endl;

		if( type == "IntegerTyID"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "IntegerTyID32"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "IntegerTyID64"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "IntegerTyID8"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "FloatTyID"){
			string val = floatvalue(constant_float);
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "DoubleTyID"){
			string val = floatvalue(constant_float);
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "StructTyID"){

			//cerr << "----- struct ------" << endl;

			const StructType* struct_type = cast<StructType>(constant->getType());

			struct_type->dump();
			constant->dump();

			string aux;

			if(constant->isNullValue()){

				string flattenedtypes = get_flattened_types(struct_type);
				vector<string> tokens = tokenize(flattenedtypes, ",");

				for ( unsigned int i = 0; i < tokens.size(); i++) {
					aux += "X,";
				}


			} else {

				for ( unsigned int i = 0; i < struct_type->getNumElements(); i++) {

					Value*         operand_i    = constant_struct->getOperand(i);

					//cerr << "operand_i" << endl;
					//operand_i->dump();

					Constant*      operand_i_const = dyn_cast<Constant>(operand_i);

					assert(operand_i_const && "Operand i must be constant");

					aux += get_flattened_vals(operand_i_const) + ",";
				}
			}

			return aux;

		} else if( type == "ArrayTyID" ){

			//cerr << "----- array ------" << endl;

			const ArrayType* array_type = cast<ArrayType>(constant->getType());

			string aux;

			if(constant->isNullValue()){

				string flattenedtypes = get_flattened_types(array_type);
				vector<string> tokens = tokenize(flattenedtypes, ",");

				for ( unsigned int i = 0; i < tokens.size(); i++) {
					aux += "X,";
				}


			} else {




				for ( unsigned int i = 0; i < array_type->getNumElements(); i++) {

					Value*         operand_i    = constant_array->getOperand(i);

					//cerr << "operand_i" << endl;
					//operand_i->dump();

					Constant*      operand_i_const = dyn_cast<Constant>(operand_i);

					assert(operand_i_const && "Operand i must be constant");

					aux += get_flattened_vals(operand_i_const) + ",";
				}
			}

			return aux;
			
		} else if( type == "PointerTyID" ){

			//cerr << "constant";
			if(constant_pointer_null){
				return "constant_0";
			} else if (constant_global) {
				constant_global->dump();
				//cerr << "address of : " << "global_" + constant_global->getName().str() << endl;
				//cerr << "is: " << given_addr["global_" + constant_global->getName().str()];
				return "constant_" + itos(given_addr["global_" + constant_global->getName().str()]);
			} else if(gepop){
				cerr << "gepop " << endl;
				gepop->dump();
				gepop->getOperand(0)->getType()->dump();
				
				string name_base = "global_" + gepop->getOperand(0)->getName().str();

				
				int b = 0;
				string offset_tree = get_offset_tree(gepop->getType(), &b);

				int base = given_addr[name_base];
				cerr << "name_base " << name_base << " base " << base << endl;

				vector<int> indexes = get_indexes_gepop(gepop);

				string indexes_str;
				for( vector<int>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
					indexes_str += itos(*it) + ",";
				}
				


				int offset = get_offset(indexes, offset_tree);

				int addr = base + offset;

				cerr << "tree " << offset_tree << " indexes " << indexes_str << " offset " << offset << " addr " << addr << endl;

				return "constant_" + itos(addr);



			} else {
				assert(0 && "Error in global pointer initialization");
			}



		} else {
			cerr << type << endl;
			assert( 0 && "Unknown initializer type");
		}

	}

	void get_given_addr(Module& M){

		glo_iterator(M,gl){
			string             name         = string("global" UNDERSCORE) + gl->getName().str();
			const PointerType* pointertype  = cast<PointerType>(gl->getType());
			const Type*        type_t       = pointertype->getElementType();
			given_addr[name] = current_addr;
			current_addr += get_size(type_t);
		}
	}

	virtual bool runOnModule(Module &M) {

		vector<VarInit> global_var_inits;

		get_given_addr(M);

		glo_iterator(M,gl){

			cerr << "--- global ";
			gl->dump();
			//cerr << "hasInitializer " << gl->hasInitializer() << endl;

			string             name         = string("global" UNDERSCORE) + gl->getName().str();
			const PointerType* pointertype  = cast<PointerType>(gl->getType());
			const Type*        type_t       = pointertype->getElementType();

			GlobalVariable*    global_var   = cast<GlobalVariable>(gl);

			string types = get_flattened_types(type_t);
			string vals;

			if(gl->hasInitializer()){
				Constant* constant     = global_var->getInitializer();
				vals  = get_flattened_vals(constant);
			} else {
				vector<string> tokens = tokenize(types,",");
				for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
					vals += "X,";
				}
			}

			//cerr << "types " << types << endl;
			//cerr << "vals  " << vals  << endl;

			VarInit varinit = {name, types, vals };

			global_var_inits.push_back(varinit);


			//cerr << "name " << name << " addr " << current_addr << endl;

		}

		BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();
		for( vector<VarInit>::iterator it = global_var_inits.begin(); it != global_var_inits.end(); it++ ){


			string name           = it->name;
			string type           = it->type;
			string initialization = it->initialization;

			GlobalVariable* c1 = make_global_str(M, name);
			GlobalVariable* c2 = make_global_str(M, type);
			GlobalVariable* c3 = make_global_str(M, initialization);
	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "global_var_init" ,
						Type::getVoidTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
			params.push_back(pointerToArray(M,c1));
			params.push_back(pointerToArray(M,c2));
			params.push_back(pointerToArray(M,c3));
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

		}

		return false;
	}
};

struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		{MainArgs         pass;   pass.runOnModule(M);}
		{FillNames        pass;   pass.runOnModule(M);}
		{SeparateGetElm   pass;   pass.runOnModule(M);}
		{GlobalInit       pass;   pass.runOnModule(M);}
		{CallInstr        pass;   pass.runOnModule(M);}
		{SelectInstr      pass;   pass.runOnModule(M);}
		{BinaryOp         pass;   pass.runOnModule(M);}
		{CastInstr        pass;   pass.runOnModule(M);}
		{LoadStore        pass;   pass.runOnModule(M);}
		{IcmpInstr        pass;   pass.runOnModule(M);}
		{BrInstr          pass;   pass.runOnModule(M);}
		{BbMarks          pass;   pass.runOnModule(M);}
		{AllocaInstr      pass;   pass.runOnModule(M);}
		{BeginEnd         pass;   pass.runOnModule(M);}
		{GetelementPtr    pass;   pass.runOnModule(M);}

		return false;
	}
};


struct AllExceptLS: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	AllExceptLS() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		{FillNames        pass;   pass.runOnModule(M);}
		{SeparateGetElm   pass;   pass.runOnModule(M);}
		{GlobalInit       pass;   pass.runOnModule(M);}
		{CallInstr        pass;   pass.runOnModule(M);}
		{SelectInstr      pass;   pass.runOnModule(M);}
		{BinaryOp         pass;   pass.runOnModule(M);}
		{CastInstr        pass;   pass.runOnModule(M);}
		//{LoadStore        pass;   pass.runOnModule(M);}
		{IcmpInstr        pass;   pass.runOnModule(M);}
		{BrInstr          pass;   pass.runOnModule(M);}
		{BbMarks          pass;   pass.runOnModule(M);}
		{AllocaInstr      pass;   pass.runOnModule(M);}
		{BeginEnd         pass;   pass.runOnModule(M);}
		{GetelementPtr    pass;   pass.runOnModule(M);}

		return false;
	}
};



// Identifiers

char FillNames::ID = 0;
static RegisterPass<FillNames> FillNames(           "instr_fill_names"      , "Fills operands and Block Names" );

char BinaryOp::ID = 0;
static RegisterPass<BinaryOp> BinaryOp(             "instr_binaryop"        , "Instrument binary operations" );

char SelectInstr::ID = 0;
static RegisterPass<SelectInstr> SelectInstr(       "instr_select"          , "Instrument select operations" );

char CastInstr::ID = 0;
static RegisterPass<CastInstr> CastInstr(           "instr_castinstr"       , "Instrument cast operations" );

char LoadStore::ID = 0;
static RegisterPass<LoadStore> LoadStore(           "instr_loadstore"       , "Instrument load/store operations" );

char SeparateGetElm::ID = 0;
static RegisterPass<SeparateGetElm> SeparateGetElm  ( "separate_getelem"    , "Separate GetElementPtr from load/store instructions" );

char IcmpInstr::ID = 0;
static RegisterPass<IcmpInstr> IcmpInstr(           "instr_icmpinstr"       , "Instrument comparison operations" );

char BrInstr::ID = 0;
static RegisterPass<BrInstr> BrInstr(               "instr_brinstr"         , "Instrument branch operations" );

char CallInstr::ID = 0;
static RegisterPass<CallInstr> CallInstr(           "instr_callinstr"       , "Instrument call operations" );

char BbMarks::ID = 0;
static RegisterPass<BbMarks> BbMarks(               "instr_bbmarks"         , "Instrument Basic-Blocks" );

char AllocaInstr::ID = 0;
static RegisterPass<AllocaInstr> AllocaInstr(       "instr_alloca"          , "Instrument alloca operations" );

char GetelementPtr::ID = 0;
static RegisterPass<GetelementPtr> GetelementPtr(   "instr_getelementptr"   , "Instrument getelementptr operations" );

char BeginEnd::ID = 0;
static RegisterPass<BeginEnd> BeginEnd(             "instr_beginend"        , "Instrument begin and end of program" );

char GlobalInit::ID = 0;
static RegisterPass<GlobalInit> GlobalInit(         "instr_globalinit"      , "Initialize global variables" );

char MainArgs::ID = 0;
static RegisterPass<MainArgs> MainArgs(             "main_args"             , "main arguments" );

char All::ID = 0;
static RegisterPass<All> All(                        "instr_all"            , "Instrument all operations" );

char AllExceptLS::ID = 0;
static RegisterPass<AllExceptLS> AllExceptLS(        "instr_all_except_ls"            , "Instrument all operations" );


