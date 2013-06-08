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


typedef struct Variable {
	int type;
	string content;
} Variable;



map<string, Variable> variables;



void binary_op(char* dst, char* op1, char* op2, char* operation){
	printf("operación binaria %s %s %s %s\n", dst, op1, op2, operation);
	variables[string(dst)].content = string(op1) + "+" + string(op2);
}

void load_instr(char* dst, char* addr){
	printf("load instruction %s %s\n", dst, addr);
}

void store_instr(char* src, char* addr){
	printf("store instruction %s %s\n", src, addr);
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
		printf("%s\n", it->second.content.c_str() );
	}
	
}

