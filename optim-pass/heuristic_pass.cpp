/*
 * =====================================================================================
 * /
 * |     Filename:  heuristic_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  01/29/2014 01:19:20 PM
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


#include "/media/disk/release/back-end/sqlite3.h"
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
		default: assert(0 && "Unknown Operation");

	}
}


string negation(string predicate){

	if( predicate == "="  ) return "#";
	if( predicate == ">"  ) return "<=";
	if( predicate == ">=" ) return "<";
	if( predicate == "<"  ) return ">=";
	if( predicate == "<=" ) return ">";
	if( predicate == "#"  ) return "=";
	assert(0 && "Unknown Operation");

}


void generate_static_conds(Function* fn, BasicBlock* bb, BranchInst* instr, string& cond_pos, string& cond_neg){

	CmpInst* cmp_instr = cast<CmpInst>(instr->getOperand(0));

	cond_pos = fn->getName().str() + "_" + bb->getName().str() + "." + get_predicate(cmp_instr);
	cond_neg = fn->getName().str() + "_" + bb->getName().str() + "." + negation(get_predicate(cmp_instr));

}

struct PathFinder: public ModulePass {

	static char ID;
	PathFinder() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		map<string, map<string, string> > conectivity_matrix;
		set<string> bbs;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
			bbs.insert(fun->getName().str() + "_" + bb->getName().str() );
		}
		}


		mod_iterator(M, fun){
		fun_iterator(fun,bb){

			string fn_name = fun->getName().str();
			string bb_name =  bb->getName().str();
			string bb_name_c = fn_name + "_" + bb_name;

			Instruction* term = bb->getTerminator();
			//term->dump();
			if( BranchInst::classof(term) ){

				BranchInst* in_b = cast<BranchInst>(term);
				if(in_b->isConditional()){
					//cerr << "conditional" << endl;

					string name1 = in_b->getSuccessor(0)->getName().str();
					string name2 = in_b->getSuccessor(1)->getName().str();

					string bb_name_1 = fn_name + "_" + bb_name;
					string bb_name_2 = fn_name + "_" + name1;
					string bb_name_3 = fn_name + "_" + name2;

					string cond_pos;
					string cond_neg;
					
					generate_static_conds(fun, bb, in_b, cond_pos, cond_neg);

					conectivity_matrix[bb_name_1][bb_name_2] = cond_pos;
					conectivity_matrix[bb_name_1][bb_name_3] = cond_neg;


				} else {
					//cerr << "inconditional" << endl;

					string name1 = in_b->getSuccessor(0)->getName().str();

					string bb_name_1 = fn_name + "_" + bb_name;
					string bb_name_2 = fn_name + "_" + name1;

					conectivity_matrix[bb_name_1][bb_name_2] = "true";
					
				}

			}

		}}

		FILE* file = fopen("/tmp/pathfinder.dot", "w");
		fprintf(file, "digraph G {\n");
		for( set<string>::iterator it = bbs.begin(); it != bbs.end(); it++ ){
			for( set<string>::iterator it2 = bbs.begin(); it2 != bbs.end(); it2++ ){
				string bb1 = *it;
				string bb2 = *it2;
				if( conectivity_matrix[bb1][bb2] != "" )
					fprintf(file, "%s -> %s [label=\"%s\"]\n", bb1.c_str(), bb2.c_str(), conectivity_matrix[bb1][bb2].c_str() );
			}
			
		}
		fprintf(file, "}\n");
		fclose(file);
		
		system("cd /tmp/; cat pathfinder.dot | dot -Tpng > pathfinder.png; eog pathfinder.png;");


		return false;
	}
};


char PathFinder::ID = 0;
static RegisterPass<PathFinder> PathFinder( "pathfinder", "Finds static paths to target");

