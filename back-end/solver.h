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

#ifndef _SOLVER_H_
#define _SOLVER_H_

#include <stdio.h>
#include <string>
#include <set>
#include <map>
#include <vector>
#include "operators.h"


using namespace std;



typedef struct Condition {
	string cond;
	string function;
	set<string> joints;
} Condition;




void clean_conditions_stack(string name);


/**
 * @brief dumps smtlib variable declarations
 *
 * @param FILE file to dump
 */
void dump_variables(FILE* file = stdout);

/**
 * @brief Dumps smtlib constraints to file
 *
 * @param FILE: file to dump
 */
void dump_conditions(FILE* file = stdout);

/**
 * @brief Dumps smtlib header
 *
 * @param file
 */
void dump_header(FILE* file = stdout);

/**
 * @brief Dumps smtlib tail
 *
 * @param file
 */
void dump_tail(FILE* file = stdout);

/**
 * @brief Dumps smtlib instructions to get variable values
 *
 * @param file
 */
void dump_get(FILE* file = stdout);

/**
 * @brief Dumps smtlib assigns
 *
 * @param file
 */
void dump_assigns(FILE* file = stdout);

/**
 * @brief Assigns variables real-values according to smt solution
 */
void get_values();

/**
 * @brief Returs true if the current problem is solvable (SAT)
 *
 * @return 
 */
bool solvable_problem();

void flat_problem();

/**
 * @brief Inserts variable name in the list of variables
 *
 * @param name
 */
void insert_variable(string name, string position);

/**
 * @brief String to integer
 *
 * @param str
 *
 * @return 
 */
int stoi(string str);

/**
 * @brief Extracts the condition from a boolean assign ( extract_condition(bool a = (b>2)) gives b>2 )
 *
 * @param content assign sentence to analyse
 *
 * @return 
 */
string extract_condition(string content);

/**
 * @brief push a condition in the stack of conditions
 *
 * @param condition
 */
void push_condition(string condition, string function, vector<string> joints);

/**
 * @brief Negates a condition
 *
 * @param condition
 *
 * @return 
 */
string negation(string condition);

/**
 * @brief Return the last condition assigned to a variable
 *
 * @param name
 *
 * @return 
 */
string get_last_condition(string name);

/**
 * @brief Actual name of a variable
 *
 * @param name
 *
 * @return 
 */
string actual(string name);

/**
 * @brief Past name of a variable 
 *
 * @param name
 *
 * @return 
 */
string past(string name);

/**
 * @brief Type of a variable
 *
 * @param name
 *
 * @return 
 */
string get_type(string name);

string name_without_suffix(string name);


void set_name_hint(string name, string hint);



void dump_flatened_variables(FILE* file = stdout );

void dump_flatened_conditions(FILE* file = stdout );

bool is_number(const std::string& s) ;


bool check_name(string name);
bool check_mangled_name(string name);
bool check_unmangled_name(string name);
void settype(string name, string type);

/**
 * @brief Name of a variable
 *
 * @param input
 *
 * @return 
 */
string name( string input, string fn_name = "" );



void set_real_value(string varname, string value, string fn_name );

void set_real_value(string varname, string value );

string content( string name );


string realvalue(string varname);


vector<string> tokenize(const string& str,const string& delimiters);


void assign_instruction(string src, string dst, string fn_name);


void binary_instruction(string dst, string op1, string op2, string operation);


int show_problem();


void print_path_stack();
void push_path_stack(bool step);

#endif /* end of include guard: _SOLVER_H_ */

