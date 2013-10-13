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
#include <assert.h>
#include "database.h"
#include "utils.h"
#include "options.h"

using namespace std;




typedef struct NameAndPosition{
	string name;
	string position;
} NameAndPosition;


inline bool operator<(const NameAndPosition& lhs, const NameAndPosition& rhs)
{
  return lhs.name > rhs.name;
}



class Operators {
public:
	Operators ();
	virtual ~Operators ();

	void binary_op(char*, char*, char*, char*);
	void cast_instruction(char*, char*, char*);
	void load_instr(char*, char*);
	void store_instr(char*, char*);
	void store_instr_2(char* _src, char* _addr);
	void load_instr_2(char* _dst, char* _addr);
	void cmp_instr(char*, char*, char*, char*);
	bool br_instr_cond(char*, char*);
	void br_instr_incond();
	void begin_bb(char* a);
	void end_bb(char* a);
	void alloca_instr(char* a, char* b);
	void begin_sim();
	void end_sim();
	void getelementptr(char*, char*, char*, char*);
	void global_var_init(char* _name,char* _type, char* _value);
	void CallInstr( char* _fn_name, char* _oplist, char* _fn_oplist, char* _ret_to );
	void Free_fn( char* _fn_name );
	void NonAnnotatedCallInstr( char* _fn_name, char* _ret_to, char* _ret_type );
	void ReturnInstr(char* _retname );
	void BeginFn(char* _fn_name);
	void select_op(char* dest, char* cond, char* sel1, char* sel2 );
	string get_actual_function();

private:
	bool see_each_problem;

	int alloca_pointer = 0;
	vector<pair<string, string> > callstack;

	string actual_function;
	string actual_bb;

	bool propagate_constants;
	bool exit_on_insert;
	map<string, string> map_pos_to_last_store;
	int get_offset(vector<string> indexes, string offset_tree, string* remaining_tree);

	
	string name( string input, string fn_name = "" );
	bool check_mangled_name(string name);
	string get_type(string name);
	void set_name_hint(string name, string hint);
	void set_offset_tree( string varname, string tree );
	void push_path_stack(bool step);
	void print_path_stack();
	string realvalue(string varname);
	bool debug;
};





/**
 * @brief Called when a binary operation is performed among two variables
 *
 * @param dst: Destination name
 * @param op1: First operand name
 * @param op2: Second operand name
 * @param operation: Operation kind
 */
extern "C" void binary_op(char*, char*, char*, char*);

extern "C" void cast_instruction(char*, char*, char*);

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
extern "C" bool br_instr_cond(char*, char*);

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

extern "C" void getelementptr(char*, char*, char*, char*);

extern "C" void global_var_init(char* _name,char* _type, char* _value);
extern "C" void CallInstr( char* _fn_name, char* _oplist, char* _fn_oplist, char* _ret_to );
extern "C" void Free_fn( char* _fn_name );

extern "C" void NonAnnotatedCallInstr( char* _fn_name, char* _ret_to, char* _ret_type );

extern "C" void ReturnInstr(char* _retname );
extern "C" void BeginFn(char* _fn_name);

extern "C" void select_op(char* dest, char* cond, char* sel1, char* sel2 );



#endif /* end of include guard: _OPERATORS_H_ */

