/*
 * =====================================================================================
 * /
 * |     Filename:  operators.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/15/2013 05:27:48 PM
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

#include <stdio.h>
#include <string>
#include <map>
#include <sstream>
#include <vector>
#include <set>
#include <boost/regex.hpp>

#define debug false
#define SIZE_STR 512

extern "C" void binary_op(char*, char*, char*, char*);
extern "C" void load_instr(char*, char*);
extern "C" void store_instr(char*, char*);
extern "C" void cmp_instr(char*, char*, char*, char*);
extern "C" bool br_instr_cond(char*);
extern "C" void br_instr_incond();
extern "C" void begin_bb(char* a);
extern "C" void end_bb(char* a);
extern "C" void alloca_instr(char* a, char* b);
extern "C" void begin_sim();
extern "C" void end_sim();

using namespace std;

int alloca_pointer = 0;

typedef struct Variable {
	string real_value;
	string type;
	vector<string> contents;
} Variable;

map<string, Variable> variables;
set<string> variable_names;
vector<string> conditions;

string realvalue(string name){

	if( name.find("constant") != string::npos )
		return name.substr(9);
	else if( variables[name].real_value == "" )
		return "0";
	else
		return variables[name].real_value;

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



string actual(string name){
	stringstream ret; ret << name << "_" << variables[name].contents.size();
	return ret.str();
}

string past(string name){

	stringstream ret;
	if(variables[name].contents.size() == 0)
		ret << name << "_" << "initial";
	else 
		ret << name << "_" << variables[name].contents.size()-1;
	return ret.str();
}

string name( string input ){

	if(input.find("constant") != string::npos ){
		int ini = 9;
		string interm = input.substr(ini);
		int len = interm.find("_");
		string final = interm.substr(0, len);

		return final;
	} else {
		return input;
	}

}

void insert_variable(string name){

	if( name.find("constant") != string::npos )
		return;

	//if(variables[name].contents.size() == 0)
		//return;

	variable_names.insert(name);

}


int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}



void assign_instruction(string src, string dst){

	stringstream content;

	content << name(actual(dst)) << " = " << name(past(src));
	variables[string(dst)].contents.push_back( content.str() );

	//insert_variable(actual(dst));
	insert_variable(past(src));

	variables[dst].real_value = realvalue(src);

	if( variables[dst].type == "" )
		variables[dst].type = variables[src].type;
	if( variables[src].type == "" )
		variables[src].type = variables[dst].type;

}


void binary_instruction(string dst, string op1, string op2, string operation){

	stringstream content;
	content << name( actual(dst) ) << " = " << name(past(op1)) << " " << operation << " " << name(past(op2));
	variables[dst].contents.push_back( content.str() );

	//insert_variable(actual(dst));
	insert_variable(past(op1));
	insert_variable(past(op2));

	if( variables[dst].type == "" )
		variables[dst].type = variables[op1].type;
	if( variables[op1].type == "" )
		variables[op1].type = variables[dst].type;


	if(operation == "<="){
		variables[dst].real_value = ( stoi(realvalue(op1) ) <= stoi( realvalue(op2) ) )?"true":"false";
	}

	if(operation == "+"){
		stringstream result; result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		variables[dst].real_value = result.str();
	}

	if(operation == "-"){
		stringstream result; result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		variables[dst].real_value = result.str();
	}


}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){
	string dst = string(_dst);
	string op1 = string(_op1);
	string op2 = string(_op2);
	string operation = string(_operation);

	binary_instruction(dst, op1, op2, operation);

	debug && printf("\e[31m binary_operation %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _op1, _op2, _operation, 
			                                                        op1.c_str(), realvalue(op1).c_str(),
									        op2.c_str(), realvalue(op2).c_str(),
										_dst, realvalue(dst).c_str() );
}

void load_instr(char* _dst, char* _addr){
	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem_" + realvalue(addr);

	assign_instruction(src, dst);

	debug && printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _addr,
								    addr.c_str(), realvalue(addr).c_str(),
								    src.c_str(), realvalue(src).c_str(),
							            dst.c_str(), realvalue(dst).c_str()
								    );
}



void store_instr(char* _src, char* _addr){
	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem_" + realvalue(string(_addr)) ;
	assign_instruction(src, dst);

	debug && printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",_src, _addr,
			                                           src.c_str(), realvalue(src).c_str(),
								   addr.c_str(), realvalue(addr).c_str(),
								   dst.c_str(), realvalue(dst).c_str() );


}



void cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){


	string dst  = string(_dst);
	string cmp1 = string(_cmp1);
	string cmp2 = string(_cmp2);
	string type = string(_type);

	//printf("real_value cmp1 %s\n", realvalue(cmp1).c_str() );
	//printf("real_value cmp2 %s\n", realvalue(cmp2).c_str() );
	

	binary_instruction(dst, cmp1, cmp2, type);

	debug && printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _cmp1, _cmp2, _type, 
			                                                 cmp1.c_str(), realvalue(cmp1).c_str(),
									 cmp2.c_str(), realvalue(cmp2).c_str(),
									 dst.c_str(), realvalue(dst).c_str() );
}

string extract_condition(string content){
	int n = (int)content.find("=") + 2;
	return content.substr(n);
}

void push_condition(string condition){

	conditions.push_back( condition );
}


string negation(string condition){

	vector<string> tokens = tokenize(condition, " ");

	if( tokens[1] == "<=" ) return tokens[0] + " > " + tokens[2];

	return condition;
}

string get_last_condition(string name){

	string content = variables[name].contents[variables[name].contents.size()-1];
	string condition = extract_condition(content);

	return condition;

}

bool br_instr_cond(char* _cmp){

	string cmp = string(_cmp);

	debug && printf("\e[31m conditional_branch_instr %s\e[0m. %s %s\n", _cmp, cmp.c_str(), realvalue(cmp).c_str() );

	for( vector<string>::iterator it = variables[cmp].contents.begin(); it != variables[cmp].contents.end(); it++ ){
		debug && printf("\e[32m content \e[0m %s\n", it->c_str());
	}

	string condition = get_last_condition(cmp);

	if(realvalue(cmp) == "true"){
		push_condition(negation(condition));

	} else {
		push_condition(condition);

	}


	return variables[cmp].real_value == "true";

}

void br_instr_incond(){

	debug && printf("\e[31m inconditional_branch_instr\e[0m\n" );

}

void begin_bb(char* name){
	debug && printf("\e[31m begin_bb %s \e[0m\n", name );
}

void alloca_instr(char* _reg, char* _type){

	string reg = string(_reg);
	string type = string(_type);

	stringstream rvalue; rvalue << alloca_pointer; 
	variables[reg].real_value = rvalue.str();

	stringstream mem_var; mem_var << "mem_" << rvalue.str().c_str();

	variables[mem_var.str()].real_value = "0";

	variables[mem_var.str()].type = type;

	alloca_pointer++;

	debug && printf("\e[31m alloca_instr %s %s\e[0m. %s %s %s %s\n",reg.c_str(), type.c_str(), reg.c_str(), realvalue(reg).c_str(), mem_var.str().c_str(), realvalue(mem_var.str()).c_str() );
}

void end_bb(char* name){
	debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

void begin_sim(){
	debug && printf("\e[31m Begin Simulation\e[0m\n" );
}

void dump_assigns(FILE* file = stdout){
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){


			vector<string> tokens = tokenize(*it2, " ");
		
			//printf("\e[31m %s \e[0m\n", it2->c_str() );
			if(tokens.size() == 5){
				if( tokens[3] == "<=" ){
					continue;
				}
				debug && fprintf(file,"(assert (= %s (%s %s %s)))\n", tokens[0].c_str(), tokens[3].c_str(), tokens[2].c_str(), tokens[4].c_str() );
			} else {
				debug && fprintf(file,"(assert (= %s %s))\n", tokens[0].c_str(), tokens[2].c_str() );
			}



		}
		
	}
}

string type(string name){
	if (variables[name].type == "IntegerTyID")
		return "Int";
	else
		return "";
}

string get_type(string name){

	int s1 = name.find("_");
	int s2 = name.find("_", s1+1);
	string name_without_suffix = name.substr(0,s2);

	return type(name_without_suffix);

}



void dump_variables(FILE* file = stdout){

	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(declare-fun %s () %s)\n", tokens[0].c_str(), type.c_str());
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}
	

}

void dump_conditions(FILE* file = stdout){

	for( vector<string>::iterator it = conditions.begin(); it != conditions.end(); it++ ){


		vector<string> tokens = tokenize(*it, " ");



		fprintf(file,"(assert (%s %s %s))\n", tokens[1].c_str(), tokens[0].c_str(), tokens[2].c_str() );
		//debug && printf("\e[33m %s \e[0m\n", it->c_str() );



	}
	
	fprintf(file,"(check-sat)\n");


}

void dump_header(FILE* file = stdout){
	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-logic QF_NIA)\n");

}

void dump_tail(FILE* file = stdout){
	fprintf(file,"(exit)\n");
}

bool solvable_problem(){


	stringstream filename;
	filename << "/tmp/z3_" << rand() << ".smt2";
	FILE* file = fopen(filename.str().c_str(), "w");
	vector<string> ret_vector;

	dump_header(file);
	dump_variables(file);
	dump_assigns(file);
	dump_conditions(file);
	dump_tail(file);

	fclose(file);

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	
	command << "z3 " << filename.str();

	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);

	bool sat = 0;

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		if( it->substr(0,3) == "sat" ) sat = 1;
	}
	
	return sat;
	
	
}

void dump_get(FILE* file = stdout){


	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(get-value (%s))\n", tokens[0].c_str() );
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}

}

void get_values(){

	stringstream filename;
	filename << "/tmp/z3_" << rand() << ".smt2";
	FILE* file = fopen(filename.str().c_str(), "w");
	vector<string> ret_vector;

	dump_header(file);
	dump_variables(file);
	dump_assigns(file);
	dump_conditions(file);
	dump_get(file);
	dump_tail(file);

	fclose(file);

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	
	command << "z3 " << filename.str();

	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);

	bool sat = 0;

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		if( it->find("((") == string::npos ) continue;
		vector<string> tokens = tokenize(*it, "() ");
		variables[ tokens[0] ].real_value = tokens[1];
		debug && printf("%s %s\n", tokens[0].c_str(), tokens[1].c_str() );
	}
	

	//for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		//if( it->substr(0,3) == "sat" ) break;
	//}
	
}

void end_sim(){
	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	//dump_header();
	//dump_variables();
	//dump_assigns();
	//dump_conditions();
	//dump_tail();
	
	printf("solvable_problem %d\n", solvable_problem() );
	get_values();
	
}

