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



void binary_op(char* a, char* b, char* c, char* d){
	printf("operación binaria %s %s %s %s\n", a, b, c, d);
	variables[string(a)].content = string(b) + "+" + string(d);
}

void load_instr(char* a, char*b){
	printf("load instruction %s %s\n", a, b);
}

void store_instr(char* a, char*b){
	printf("store instruction %s %s\n", a, b);
}

void cmp_instr(char* a, char*b, char* c, char* d){

	printf("cmp_instr %s %s %s %s\n", a, b, c, d);

}


bool br_instr_cond(char* a){

	printf("branch_instr %s\n", a );
	return true;

}

void br_instr_incond(){

	printf("branch_instr\n" );

}


void begin_bb(char* a){
	printf("begin_bb %s\n", a );
}

void alloca_instr(char* a, char* b){
	printf("alloca_instr %s %s\n", a, b );
}

void end_bb(char* a){
	printf("end_bb %s\n", a );
}

void begin_sim(){
	printf("Begin Simulation\n" );
}

void end_sim(){
	printf("End Simulation\n" );
}

