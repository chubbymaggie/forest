/*
 * =====================================================================================
 * /
 * |     Filename:  solver.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/12/2013 02:44:33 PM
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
#include <set>
#include <map>
#include <vector>
#include "operators.h"

#ifndef _SOLVER_H_
#define _SOLVER_H_

using namespace std;

void dump_variables(FILE*);
void dump_conditions(FILE*);
void dump_header(FILE* file);
void dump_tail(FILE* file);
void dump_get(FILE* file);
void dump_assigns(FILE* file);
void get_values();
bool solvable_problem();
void insert_variable(string name);
int stoi(string str);
string extract_condition(string content);
void push_condition(string condition);
string negation(string condition);
string get_last_condition(string name);
string actual(string name);
string past(string name);
string type(string name);
string get_type(string name);
string name( string input );

#endif /* end of include guard: _SOLVER_H_ */

