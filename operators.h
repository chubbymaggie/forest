/*
 * =====================================================================================
 * /
 * |     Filename:  operators.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/12/2013 02:20:13 PM
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
#include <unistd.h>
#include <stdlib.h>

#ifndef _OPERATORS_H_
#define _OPERATORS_H_

using namespace std;

typedef struct Variable {
	string real_value;
	string type;
	vector<string> contents;
} Variable;

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

vector<string> tokenize(const string& str,const string& delimiters);

bool br_instr_cond(char* _cmp);
void br_instr_incond();
void begin_bb(char* name);
void alloca_instr(char* _reg, char* _type);
void end_bb(char* name);
void begin_sim();
void end_sim();
void assign_instruction(string src, string dst);
void binary_instruction(string dst, string op1, string op2, string operation);
void binary_op(char* _dst, char* _op1, char* _op2, char* _operation);
void load_instr(char* _dst, char* _addr);
void store_instr(char* _src, char* _addr);
void cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type);

#endif /* end of include guard: _OPERATORS_H_ */

