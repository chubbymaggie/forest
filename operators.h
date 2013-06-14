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

#ifndef _OPERATORS_H_
#define _OPERATORS_H_

#include <stdio.h>
#include <string>
#include <map>
#include <sstream>
#include <vector>
#include <set>
#include <unistd.h>
#include <stdlib.h>
#include "database.h"


using namespace std;

typedef struct Variable {
	string real_value;
	string type;
	vector<string> contents;
} Variable;

/**
 * @brief Called when a binary operation is performed among two variables
 *
 * @param dst: Destination name
 * @param op1: First operand name
 * @param op2: Second operand name
 * @param operation: Operation kind
 */
extern "C" void binary_op(char*, char*, char*, char*);

/**
 * @brief Called when a load instruction assigns the value of a memory position (pointed by the register named addr) to a register
 *
 * @param _dst: name of the destination register
 * @param _addr: name of the register that contains the address
 */
extern "C" void load_instr(char*, char*);

/**
 * @brief Called when a store instruction assigns the value of a register to a memory position
 *
 * @param _src: register name
 * @param _addr: name of the register that contains the address of the store
 */
extern "C" void store_instr(char*, char*);

/**
 * @brief Comparison instruction
 *
 * @param _dst: name of the destination
 * @param _cmp1: Name of the first register
 * @param _cmp2: Name of the second register
 * @param _type: Type of comparison
 */
extern "C" void cmp_instr(char*, char*, char*, char*);

/**
 * @brief Conditional branch instruction
 *
 * @param _cmp: Name of the register that contains the branch condition
 *
 * @return 
 */
extern "C" bool br_instr_cond(char*);

/**
 * @brief Inconditional branch instruction
 */
extern "C" void br_instr_incond();

/**
 * @brief  Begin basic Block
 *
 * @param name: Name of the basic block
 */
extern "C" void begin_bb(char* a);

/**
 * @brief End basic block
 *
 * @param name
 */
extern "C" void end_bb(char* a);

/**
 * @brief Function that is called when a new variable is allocated
 *
 * @param _reg: name of the register that holds the position of new variable in memory
 * @param _type: Data type of allocated value
 */
extern "C" void alloca_instr(char* a, char* b);

/**
 * @brief Function that is called at the begining of simulation
 */
extern "C" void begin_sim();

/**
 * @brief Function that is called at the end of simulation
 */
extern "C" void end_sim();

extern "C" void getelementptr(char*, char*, char*);

/**
 * @brief Returns actual value of a variable
 *
 * @param name name of the variable
 *
 * @return 
 */
string realvalue(string name);

/**
 * @brief Tokenizes a string
 *
 * @param str: string to cut
 * @param delimiters: Delimiters
 *
 * @return 
 */
vector<string> tokenize(const string& str,const string& delimiters);

/**
 * @brief Called when a variable is assigned to another
 *
 * @param src: Origin variable name
 * @param dst: Destination variable name
 */
void assign_instruction(string src, string dst);

/**
 * @brief Called when a binary operation is performed among two variables
 *
 * @param dst: Destination name
 * @param op1: First operand name
 * @param op2: Second operand name
 * @param operation: Operation kind
 */
void binary_instruction(string dst, string op1, string op2, string operation);

#endif /* end of include guard: _OPERATORS_H_ */

