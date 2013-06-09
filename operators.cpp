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

}

void binary_instruction(string dst, string op1, string op2, string operation){

	stringstream content;
	content << actual(dst) << " = " << past(op1) << " " << "+" << " " << past(op2);
	variables[dst].contents.push_back( content.str() );
}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){
	printf("operación binaria %s %s %s %s\n", _dst, _op1, _op2, _operation);
	string dst = string(_dst);
	string op1 = string(_op1);
	string op2 = string(_op2);
	string operation = string(_operation);
	binary_instruction(dst, op1, op2, operation);
}

void load_instr(char* _dst, char* _addr){
	printf("load instruction %s %s\n", _dst, _addr);
	string dst = string(_dst);
	string src = "mem_" + variables[string(_addr)].real_value;
	assign_instruction(src, dst);
}

void store_instr(char* _src, char* _addr){
	printf("store instruction %s %s\n", _src, _addr);
	string src = string(_src);
	string dst = "mem_" + variables[string(_addr)].real_value;
	assign_instruction(src, dst);
}

void cmp_instr(char* dst, char* cmp1, char* cmp2, char* type){
	printf("cmp_instr %s %s %s %s\n", dst, cmp1, cmp2, type);
}


bool br_instr_cond(char* cmp){

	printf("branch_instr %s\n", cmp );
	return true;

}

void br_instr_incond(){

	printf("branch_instr\n" );

}


void begin_bb(char* name){
	printf("begin_bb %s\n", name );
}

void alloca_instr(char* reg, char* type){
	printf("alloca_instr %s %s\n", reg, type );

	stringstream realvalue; realvalue << alloca_pointer; 
	variables[string(reg)].real_value = realvalue.str();
	alloca_pointer++;
}

void end_bb(char* name){
	printf("end_bb %s\n", name );
}

void begin_sim(){
	printf("Begin Simulation\n" );
}

void end_sim(){
	printf("End Simulation\n" );
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){
			printf("\e[31m %s \e[0m\n", it2->c_str() );
		}
		
	}
	
}

