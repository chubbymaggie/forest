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
	int type;
	vector<string> contents;
} Variable;

map<string, Variable> variables;
set<string> variable_names;


string realvalue(string name){

	if( name.find("constant") != string::npos )
		return name.substr(9);
	else if( variables[name].real_value == "" )
		return "0";
	else
		return variables[name].real_value;

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

void assign_instruction(string src, string dst){

	stringstream content;

	content << actual(dst) << " = " << past(src);
	variables[string(dst)].contents.push_back( content.str() );

	variable_names.insert(actual(dst));
	variable_names.insert(past(src));

	variables[dst].real_value = variables[src].real_value;

}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

void binary_instruction(string dst, string op1, string op2, string operation){

	stringstream content;
	content << actual(dst) << " = " << past(op1) << " " << operation << " " << past(op2);
	variables[dst].contents.push_back( content.str() );

	variable_names.insert(actual(dst));
	variable_names.insert(past(op1));
	variable_names.insert(past(op2));


	if(operation == "<="){
		variables[dst].real_value = ( stoi(variables[op1].real_value) <= stoi(variables[op2].real_value) )?"true":"false";
	}

	if(operation == "add"){
		stringstream result; result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		variables[dst].real_value = result.str();
	}

	if(operation == "sub"){
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

	printf("\e[31m binary_operation %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _op1, _op2, _operation, 
			                                                        op1.c_str(), realvalue(op1).c_str(),
									        op2.c_str(), realvalue(op2).c_str(),
										_dst, realvalue(dst).c_str() );
}

void load_instr(char* _dst, char* _addr){
	string dst = string(_dst);
	string src = "mem_" + variables[string(_addr)].real_value;

	string addr = string(_addr);
	assign_instruction(src, dst);

	printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _addr,
							            dst.c_str(), realvalue(dst).c_str(),
								    addr.c_str(), realvalue(addr).c_str(),
								    src.c_str(), realvalue(src).c_str()
								    );
}



void store_instr(char* _src, char* _addr){
	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem_" + realvalue(string(_addr)) ;
	assign_instruction(src, dst);

	printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",_src, _addr,
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

	printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _cmp1, _cmp2, _type, 
			                                                 cmp1.c_str(), realvalue(cmp1).c_str(),
									 cmp2.c_str(), realvalue(cmp2).c_str(),
									 dst.c_str(), realvalue(dst).c_str() );
}

bool br_instr_cond(char* _cmp){



	string cmp = string(_cmp);

	printf("\e[31m conditional_branch_instr %s\e[0m. %s %s\n", _cmp, cmp.c_str(), realvalue(cmp).c_str() );

	for( vector<string>::iterator it = variables[cmp].contents.begin(); it != variables[cmp].contents.end(); it++ ){
		printf("\e[32m content \e[0m %s\n", it->c_str());
	}

	//if( satisfiable(variables, cmp,  ) )

	return variables[cmp].real_value == "true";

}

void br_instr_incond(){

	printf("\e[31m inconditional_branch_instr\e[0m\n" );

}

void begin_bb(char* name){
	printf("\e[31m begin_bb %s \e[0m\n", name );
}

void alloca_instr(char* reg, char* type){

	stringstream realvalue; realvalue << alloca_pointer; 
	variables[string(reg)].real_value = realvalue.str();

	stringstream mem_var; mem_var << "mem_" << realvalue.str().c_str();

	variables[mem_var.str()].real_value = "0";

	alloca_pointer++;

	printf("\e[31m alloca_instr %s %s\e[0m. %s %s %s %s\n",reg, type, reg, variables[reg].real_value.c_str(), mem_var.str().c_str(), variables[mem_var.str()].real_value.c_str() );
}

void end_bb(char* name){
	printf("\e[31m end_bb %s\e[0m\n", name );
}

void begin_sim(){
	printf("\e[31m Begin Simulation\e[0m\n" );
}

void dump_assigns(){
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){
			printf("\e[31m %s \e[0m\n", it2->c_str() );
		}
		
	}
}

void dump_variables(){

	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
		printf("\e[32m %s \e[0m\n", it->c_str());
	}
	

}

void end_sim(){
	printf("\e[31m End Simulation\e[0m\n" );
	dump_variables();
	dump_assigns();
	
}

