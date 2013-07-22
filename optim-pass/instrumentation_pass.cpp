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


// Helper Functions

string operandname( Value* operand ){

	if( ConstantInt::classof(operand) ){

		ConstantInt* CI = dyn_cast<ConstantInt>(operand);
		int64_t val = CI->getSExtValue();
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
		return nameop1_ss.str();

	} else if( ConstantFP::classof(operand) ){

		ConstantFP* CF = dyn_cast<ConstantFP>(operand);

		stringstream nameop1_ss;

		if( operand->getType()->getTypeID() == 1){
			float val = CF->getValueAPF().convertToFloat();
			nameop1_ss << "constant" UNDERSCORE << val;
		} else {
			float val = CF->getValueAPF().convertToDouble();
			nameop1_ss << "constant" UNDERSCORE << val;
		}

		return nameop1_ss.str();
	} else if ( ConstantPointerNull::classof(operand) ){
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE "0";
		return nameop1_ss.str();
	} else if(GlobalVariable::classof(operand)){
		return "global" UNDERSCORE + operand->getName().str();
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
	}

	t->dump();
	cerr << typId << endl;

	assert(0 && "Unknown Type");

	//switch(typId){

		//case  -1: return "VoidTyID";
		//case  0: return "HalfTyID";
		//case  1: return "FloatTyID";
		//case  2: return "DoubleTyID";
		//case  3: return "X86_FP80TyID";
		//case  4: return "FP128TyID";
		//case  5: return "PPC_FP128TyID";
		//case  6: return "LabelTyID";
		//case  7: return "MetadataTyID";
		////case  8: return "X86_MMXTyID";
		//case 8: return "IntegerTyID";
		//case 10: return "FunctionTyID";
		//case 11: return "StructTyID";
		////case 12: return "ArrayTyID";
		//case 12: return "PointerTyID";
		//case 14: return "VectorTyID";

	//}

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
	if( type == "FloatTyID" ) return 4;
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

	return primary_size( last_type );

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

int sizeofstruct(const Type* t);
int get_size( const Type* t );

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



						bool is_getelement = !(in->getOperand(0)->hasName());
						GEPOperator* gepop = dyn_cast<GEPOperator>(in->getOperand(0));

						if( is_getelement && gepop ){
							in->dump();


							Value* pointer = gepop->getPointerOperand();
							User::op_iterator idxbegin = gepop->idx_begin();
							User::op_iterator idxend   = gepop->idx_end();
							vector<Value*> indices(idxbegin, idxend);

							GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);

							in->setOperand(0,getelement);


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

	map<string, vector<string> > arguments;

	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fn){

			Function::arg_iterator arg_begin = fn->arg_begin();
			Function::arg_iterator arg_end   = fn->arg_end();

			for( Function::arg_iterator it = arg_begin; it != arg_end; it++ ){

				//cerr << fn->getName().str() << " " << it->getName().str() << endl;
				//arguments[ fn->getName().str() ].push_back( it->getName().str() );
				arguments[ fn->getName().str() ].push_back( operandname(it) );
			}

			//if( arg_begin != arg_end ){
				//arg_begin->dump();
				
				//cerr << arg_begin->getName().str() << endl;
				//cerr << fn->getName().str() << endl;

			//}
		}

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CallInst::classof(in) ){

						CallInst* in_c = cast<CallInst>(in);

						string fn_name = in_c->getCalledFunction()->getName().str();

						if(fn_name == "global_var_init") continue;


						stringstream operand_list;
						for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {
							string name = operandname( in_c->getArgOperand(i) );
							operand_list << name << ",";
						}

						stringstream function_operand_list;
						vector<string> fn_operand_list = arguments[ fn_name ];

						for( vector<string>::iterator it = fn_operand_list.begin(); it != fn_operand_list.end(); it++ ){
							function_operand_list << *it << ",";
						}

						string oplist  = operand_list.str();
						string fn_oplist = function_operand_list.str();
						string ret_to = operandname( in_c );
						string ret_type = get_type_str( in_c->getType() );
						
						//cerr << fn_name << endl;
						//cerr << oplist  << endl;
						//cerr << fn_oplist << endl;

						Function::iterator fn_begin = in_c->getCalledFunction()->begin();
						Function::iterator fn_end   = in_c->getCalledFunction()->end();

						bool annotated = (fn_begin != fn_end);


						if( annotated ){

							GlobalVariable* c1 = make_global_str(M, fn_name );
							GlobalVariable* c2 = make_global_str(M, oplist );
							GlobalVariable* c3 = make_global_str(M, fn_oplist );
							GlobalVariable* c4 = make_global_str(M, ret_to );

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "CallInstr" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
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
							params.push_back(pointerToArray(M,c4));
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

string get_flattened_types(const Type* t){
	t->dump();

	string ret;
	const StructType* t_s = dyn_cast<StructType>(t);
	const ArrayType*  t_a = dyn_cast<ArrayType>(t);

	if(t_s){
		unsigned int numelems = t_s->getNumElements();

		for ( unsigned int i = 0; i < numelems; i++) {
			ret += get_flattened_types(t_s->getElementType(i));
		}

		return ret;
	} else {
		return get_type_str(t) + ",";
	}


}

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
						string subtype;

						if(type == "ArrayTyID"){
							const ArrayType* typ = cast<ArrayType>(in_a->getAllocatedType());
							const Type* typ2 = cast<Type>( element_type(typ) );
							subtype = get_type_str( typ2 );
						} else if(type == "StructTyID") {
							subtype = get_flattened_types(in_a->getAllocatedType());
							cerr << "subtype_flattened " << subtype << endl;
						} else {
							subtype = type;
						}

						//cerr << type << endl;

						
						int size = get_size( in_a->getAllocatedType() );
						stringstream size_ss; size_ss << size;

						
						
						//in_a->getAllocatedType()->dump();
						//cerr << "size: " << size << endl; fflush(stderr);


						//vector<int> sizes = get_dimensions(in_a->getType());
						//for ( unsigned int i = 0; i < sizes.size(); i++) {
							//cerr << "size: " << sizes[i] << endl;
						//}


						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, type);
						GlobalVariable* c3 = make_global_str(M, size_ss.str());
						GlobalVariable* c4 = make_global_str(M, subtype);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "alloca_instr" ,
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

						//for( op_iterator it = in_g->idx_begin(); it != in_g->idx_end(); it++ ){
							//it->dump();
						//}
						
						vector<string> indexes = get_indexes(in_g);


						const PointerType* t_p  = dyn_cast<PointerType>(in_g->getPointerOperandType());
						const ArrayType*   t_a  = dyn_cast<ArrayType>(t_p->getElementType());
						const StructType*  t_s  = dyn_cast<StructType>(t_p->getElementType());
						const Type* t_pp        = t_p->getElementType();

						//cerr << t_p << " " << t_a << endl;

						//cerr << "GetElementPtrInst2" << endl; fflush(stderr);
						//in_g->getPointerOperandType()->dump(); fflush(stderr);
						//const ArrayType* t_a = dyn_cast<ArrayType>(in_g->getPointerOperandType());

						vector<string> sizes;
						if( t_a ){
							sizes = get_nested_sizes( t_a );
						} else if (t_s) {
							sizes = get_struct_offsets(t_s);
						} else if( t_pp ){
							const Type* tp = t_p->getElementType();
							stringstream size; size << get_size(t_pp);
							sizes.push_back( "constant" UNDERSCORE + size.str() );
						}

						//cerr << "GetElementPtrInst3" << endl; fflush(stderr);



						//cerr << "result: " << nameres << endl;
						//cerr << "operand1: " << nameop1 << endl;
						//for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
							//cerr << "index: " << *it << endl;
						//}
						

						string indexes_str;
						for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
							indexes_str += *it + ",";
						}

						string nst_sizes;
						for( vector<string>::iterator it = sizes.begin(); it != sizes.end(); it++ ){
							nst_sizes += *it + ",";
						}


						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, indexes_str);
						GlobalVariable* c4 = make_global_str(M, nst_sizes);

						Value* InitFn;

						if( t_s ){
							InitFn = cast<Value> ( M.getOrInsertFunction( "getelementptr_struct" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));
						} else if( t_a || t_pp ){
							InitFn = cast<Value> ( M.getOrInsertFunction( "getelementptr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						} else {
							assert(0 && "getelementptr no pointer or struct");
						}

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

typedef struct VarInit {
	string name;
	string nelems;
	string type;
	string initialization;
} VarInit;


string itos( int value ){
	stringstream ret_ss;
	ret_ss << value;
	return ret_ss.str();
}

struct GlobalInit: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	GlobalInit() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<VarInit> global_var_inits;

		glo_iterator(M,gl){

			//gl->dump();

			string             name         = string("global" UNDERSCORE) + gl->getName().str();
			const PointerType* pointertype  = cast<PointerType>(gl->getType());
			const Type*        type_t       = pointertype->getElementType();
			string             type         = get_type_str(type_t);

			if( type == "IntegerTyID32"){

				GlobalVariable*    global_var   = cast<GlobalVariable>(gl);
				Constant*          constant     = global_var->getInitializer();
				ConstantInt*       constant_int = dyn_cast<ConstantInt>(constant);
				int64_t            val          = constant_int->getSExtValue();
				string             val_s        = itos(val);
				string             nelems       = itos(1);

				VarInit varinit = {name,nelems, type, val_s};

				global_var_inits.push_back(varinit);

			}

			if( type == "ArrayTyID" ){

				const ArrayType* t_a = cast<ArrayType>(type_t);

				string nelems = itos( product(get_dimensions(t_a)) );

				GlobalVariable*    global_var   = cast<GlobalVariable>(gl);
				Constant*          constant     = global_var->getInitializer();
				ConstantArray*     constant_a   = dyn_cast<ConstantArray>(constant);

				bool ndimensions = 0;

				stringstream val_ss;
				if( constant_a ){
					for ( unsigned int i = 0; i < constant_a->getNumOperands(); i++) {

						Value*         operand_i    = constant_a->getOperand(i);
						ConstantInt*   constant_int = dyn_cast<ConstantInt>(operand_i);
						ConstantArray* constant_arr = dyn_cast<ConstantArray>(operand_i);

						if(constant_int){
							ndimensions = 1;
							int64_t            val          = constant_int->getSExtValue();
							val_ss << val << ",";
						} else if (constant_arr){
							ndimensions = 2;
							for ( unsigned int j = 0; j < constant_a->getNumOperands(); j++) {
								Value* operand_i_2 = constant_arr->getOperand(j);
								ConstantInt* constant_int_2 = dyn_cast<ConstantInt>(operand_i_2);
								int64_t val = constant_int_2->getSExtValue();
								val_ss << val << ",";
							}


						} else {
							assert(0 && "Unknown array");
						}

					}
				}

				string val_s  = val_ss.str();

				const ArrayType* type_a = cast<ArrayType>(type_t);

				//const Type* type_e      = type_a->getElementType();
				//if(ndimensions == 1){
					//string type_e_s         = get_type_str(type_e);
				//} else if (ndimensions == 2){
					//const ConstantArray* type_e_as_array = cast<ConstantArray>(type_e);
					//type_e = type_e_as_array->getElementType();
				//}

				
				const Type* type_e      = element_type(type_a);
				string type_e_s         = get_type_str(type_e);
				

				VarInit varinit = {name,nelems, type_e_s, val_s};

				global_var_inits.push_back(varinit);

			}

		}

		for( vector<VarInit>::iterator it = global_var_inits.begin(); it != global_var_inits.end(); it++ ){

			BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();

			string name           = it->name;
			string nelems         = it->nelems;
			string type           = it->type;
			string initialization = it->initialization;

			GlobalVariable* c1 = make_global_str(M, name);
			GlobalVariable* c2 = make_global_str(M, nelems);
			GlobalVariable* c3 = make_global_str(M, type);
			GlobalVariable* c4 = make_global_str(M, initialization);
	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "global_var_init" ,
						Type::getVoidTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
			params.push_back(pointerToArray(M,c1));
			params.push_back(pointerToArray(M,c2));
			params.push_back(pointerToArray(M,c3));
			params.push_back(pointerToArray(M,c4));
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
		}

		return false;
	}
};


struct StructureSizes: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	StructureSizes() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( AllocaInst::classof(in) ){

						AllocaInst* in_a = cast<AllocaInst>(in);

						in_a->getAllocatedType()->dump();

						cerr << get_type_str(in_a->getAllocatedType()) << endl;

						cerr << get_size(in_a->getAllocatedType()) << endl;
					}
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

		//{StructureSizes pass;   pass.runOnModule(M);}
		

		{SeparateGetElm   pass;   pass.runOnModule(M);}
		//{GlobalInit     pass;   pass.runOnModule(M);}
		//{CallInstr      pass;   pass.runOnModule(M);}
		//{BinaryOp       pass;   pass.runOnModule(M);}
		//{CastInstr      pass;   pass.runOnModule(M);}
		//{LoadStore      pass;   pass.runOnModule(M);}
		//{IcmpInstr      pass;   pass.runOnModule(M);}
		//{BrInstr        pass;   pass.runOnModule(M);}
		//{BbMarks        pass;   pass.runOnModule(M);}
		//{AllocaInstr    pass;   pass.runOnModule(M);}
		//{BeginEnd       pass;   pass.runOnModule(M);}
		//{GetelementPtr  pass;   pass.runOnModule(M);}

		return false;
	}
};

// Identifiers

char FillNames::ID = 0;
static RegisterPass<FillNames> FillNames(         "instr_fill_names"    , "Fills operands and Block Names" );

char BinaryOp::ID = 0;
static RegisterPass<BinaryOp> BinaryOp(           "instr_binaryop"      , "Instrument binary operations" );

char CastInstr::ID = 0;
static RegisterPass<CastInstr> CastInstr(         "instr_castinstr"     , "Instrument cast operations" );

char LoadStore::ID = 0;
static RegisterPass<LoadStore> LoadStore(         "instr_loadstore"     , "Instrument load/store operations" );

char SeparateGetElm::ID = 0;
static RegisterPass<SeparateGetElm> SeparateGetElm( "separate_getelem"  , "Separate GetElementPtr from load/store instructions" );

char IcmpInstr::ID = 0;
static RegisterPass<IcmpInstr> IcmpInstr(         "instr_icmpinstr"     , "Instrument comparison operations" );

char BrInstr::ID = 0;
static RegisterPass<BrInstr> BrInstr(             "instr_brinstr"       , "Instrument branch operations" );

char CallInstr::ID = 0;
static RegisterPass<CallInstr> CallInstr(         "instr_callinstr"     , "Instrument call operations" );

char BbMarks::ID = 0;
static RegisterPass<BbMarks> BbMarks(             "instr_bbmarks"       , "Instrument Basic-Blocks" );

char AllocaInstr::ID = 0;
static RegisterPass<AllocaInstr> AllocaInstr(     "instr_alloca"        , "Instrument alloca operations" );

char GetelementPtr::ID = 0;
static RegisterPass<GetelementPtr> GetelementPtr( "instr_getelementptr" , "Instrument getelementptr operations" );

char BeginEnd::ID = 0;
static RegisterPass<BeginEnd> BeginEnd(           "instr_beginend"      , "Instrument begin and end of program" );

char StructureSizes::ID = 0;
static RegisterPass<StructureSizes> StructureSizes( "instr_structure_sizes"      , "Instrument structure sizes" );

char GlobalInit::ID = 0;
static RegisterPass<GlobalInit> GlobalInit( "instr_globalinit"      , "Initialize global variables" );

char All::ID = 0;
static RegisterPass<All> All(                     "instr_all"           , "Instrument all operations" );

