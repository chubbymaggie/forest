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


typedef struct Node {
	string name;
	int next_a;
	int next_b;
	string cond_a;
	string cond_b;
} Node;

int get_or_insert_node(vector<Node>& nodes, string name){
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].name == name)
			return i;
	}
	
	Node node = {name, -1, -1, "", ""};
	nodes.push_back(node);
	return nodes.size()-1;
}

void set_cond(vector<Node>& nodes, int node1, int node2, string cond){

	if(nodes[node1].cond_a == ""){
		nodes[node1].cond_a = cond;
		nodes[node1].next_a = node2;
	} else {
		nodes[node1].cond_b = cond;
		nodes[node1].next_b = node2;
	}

}

map<string, map<string, string> > inline_calls( map<string, map<string, map<string, string> > > conectivity_matrix, map<pair<string, string>, vector<string> > calls ){
// bb1, bb2, cond
//map<string, map<string, map<string, string> > > conectivity_matrix; // function, bb1, bb2, cond 
//map<pair<string, string>, vector<string> > calls; // (function and bb), functions called

	map<string, map<string, string> > ret;
	vector<Node> nodes;

	map<string, map<string, string> > bbs_main = conectivity_matrix["main"]; // bb1, bb2, cond

	for( map<string,map<string, string> >::iterator it = bbs_main.begin(); it != bbs_main.end(); it++ ){
		string bb_1 = it->first;
		map<string, string> connected = it->second;
		for( map<string,string>::iterator it2 = connected.begin(); it2 != connected.end(); it2++ ){
			string bb_2 = it2->first;
			string cond = it2->second;

			string bb1_complete = "main_" + bb_1;
			string bb2_complete = "main_" + bb_2;

			int node1 = get_or_insert_node(nodes, bb1_complete);
			int node2 = get_or_insert_node(nodes, bb2_complete);
			
			set_cond(nodes, node1, node2, cond);
		}
	}
	
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		cerr << "Node"	<< i << ": ";
		cerr << nodes[i].name << " ";
		cerr << nodes[i].next_a << " ";
		cerr << nodes[i].next_b << " ";
		cerr << nodes[i].cond_a << " ";
		cerr << nodes[i].cond_b << " ";
		cerr << endl;
	}


	for ( unsigned int i = 0; i < nodes.size(); i++) {
		string name1 = nodes[i].name;

		bool has_next_a = (nodes[i].next_a != -1);
		bool has_next_b = (nodes[i].next_b != -1);

		if(has_next_a){
			string name2 = nodes[nodes[i].next_a].name;
			string cond = nodes[i].cond_a;
			ret[name1][name2] = cond;
		}

		if(has_next_b){
			string name2 = nodes[nodes[i].next_b].name;
			string cond = nodes[i].cond_b;
			ret[name1][name2] = cond;
		}


	}

	//for( map<string, map<string, map<string, string> > >::iterator it = conectivity_matrix.begin(); it != conectivity_matrix.end(); it++ ){
		//map<string, map<string, string> > map_bbs = it->second;
		//string fn_name = it->first;
		//for( map<string,map<string, string> >::iterator it2 = map_bbs.begin(); it2 != map_bbs.end(); it2++ ){
			//string bb_1 = it2->first;
			//map<string, string> connected = it2->second;
			//for( map<string,string>::iterator it3 = connected.begin(); it3 != connected.end(); it3++ ){
				//string bb_2 = it3->first;

				//string bb1_complete = fn_name + "_" + bb_1;
				//string bb2_complete = fn_name + "_" + bb_2;

				//ret[bb1_complete][bb2_complete] = conectivity_matrix[fn_name][bb_1][bb_2];

			//}

		//}

	//}

	//for( map<pair<string, string>,vector<string> >::iterator it = calls.begin(); it != calls.end(); it++ ){


		//string fn_1   = it->first.first;
		//string bb_1   = it->first.second;
		//string bb_1_c = fn_1 + "_" + bb_1;
		//cerr << bb_1_c << endl;
		//for( vector<string>::iterator it2 = (it->second).begin(); it2 != (it->second).end(); it2++ ){
			//string fn_2 = (*it2);
			//cerr << " " << fn_2 << endl;

			////inline_calls_rec(conectivity_matrix, ret, it->first, fn_2 );
		//}
		
	//}
	
	return ret;

}



struct PathFinder: public ModulePass {

	static char ID;
	PathFinder() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		map<string, map<string, string> > conectivity_matrix_inlined; // bb1, bb2, cond
		map<string, map<string, map<string, string> > > conectivity_matrix; // function, bb1, bb2, cond 
		map<pair<string, string>, vector<string> > calls; // (function and bb), functions called


		mod_iterator(M, fun){
		fun_iterator(fun,bb){

			string fn_name = fun->getName().str();
			string bb_name =  bb->getName().str();

			Instruction* term = bb->getTerminator();
			//term->dump();
			if( BranchInst::classof(term) ){

				BranchInst* in_b = cast<BranchInst>(term);
				if(in_b->isConditional()){
					//cerr << "conditional" << endl;

					string name1 = in_b->getSuccessor(0)->getName().str();
					string name2 = in_b->getSuccessor(1)->getName().str();

					string cond_pos;
					string cond_neg;
					generate_static_conds(fun, bb, in_b, cond_pos, cond_neg);

					conectivity_matrix[fn_name][bb_name][name1] = cond_pos;
					conectivity_matrix[fn_name][bb_name][name2] = cond_neg;


				} else {
					//cerr << "inconditional" << endl;

					string name1 = in_b->getSuccessor(0)->getName().str();
					conectivity_matrix[fn_name][bb_name][name1] = "true";
					
				}

			}

		}}


		

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){
			if(CallInst::classof(in)){
				CallInst* in_c = cast<CallInst>(in);

				string fun_1 = fun->getName().str();
				string bb_1  = bb->getName().str();
				string fun_2 = in_c->getCalledFunction()->getName().str();

				calls[pair<string, string>(fun_1, bb_1)].push_back(fun_2);
			}
		}}}


		for( map<pair<string, string>,vector<string> >::iterator it = calls.begin(); it != calls.end(); it++ ){
			pair<string, string> src = it->first;
			vector<string> dst = it->second;

			for( vector<string>::iterator it2 = dst.begin(); it2 != dst.end(); it2++ ){
				cerr << src.first << "-" << src.second << ":" << *it2 << endl;
			}
			
			
		}


		conectivity_matrix_inlined = inline_calls(conectivity_matrix, calls);


		FILE* file = fopen("/tmp/pathfinder.dot", "w");
		fprintf(file, "digraph G {\n");

		for( map<string, map<string, string> >::iterator it2 = conectivity_matrix_inlined.begin(); it2 != conectivity_matrix_inlined.end(); it2++ ){
			string bb_1 = it2->first;
			map<string, string> connected = it2->second;
			for( map<string,string>::iterator it3 = connected.begin(); it3 != connected.end(); it3++ ){
				string bb_2 = it3->first;

				string bb1_complete = bb_1;
				string bb2_complete = bb_2;

				fprintf(file, "%s -> %s [label=\"%s\"]\n", bb1_complete.c_str(), bb2_complete.c_str(), conectivity_matrix_inlined[bb_1][bb_2].c_str() );

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

