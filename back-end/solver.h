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
void insert_variable(string name);

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
string type(string name);

/**
 * @brief Type of a variable
 *
 * @param name
 *
 * @return 
 */
string get_type(string name);

string name_without_suffix(string name);





void dump_flatened_variables(FILE* file = stdout );

void dump_flatened_conditions(FILE* file = stdout );

bool is_number(const std::string& s) ;



/**
 * @brief Name of a variable
 *
 * @param input
 *
 * @return 
 */
string name( string input, string fn_name = "" );








#endif /* end of include guard: _SOLVER_H_ */

