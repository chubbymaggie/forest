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
#include "concurrency.h"

using namespace std;








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

	int alloca_pointer;
	vector<pair<string, string> > callstack;

	string actual_function;
	string actual_bb;

	bool propagate_constants;
	bool exit_on_insert;
	//map<string, string> map_pos_to_last_store;
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




#endif /* end of include guard: _OPERATORS_H_ */

