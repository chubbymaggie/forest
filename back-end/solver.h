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
#include <string.h>
#include <set>
#include <map>
#include <vector>
#include "operators.h"


using namespace std;



typedef struct Condition {
	string cond;
	string function;
	set<string> joints;
	bool fuzzme;
} Condition;



typedef struct Variable {
	string real_value;
	string type;
	string name_hint;
	string content;
	string tree;
	bool is_propagated_constant;
	bool fuzzme;
} Variable;


typedef struct NameAndPosition{
	string name;
	string position;
} NameAndPosition;


inline bool operator<(const NameAndPosition& lhs, const NameAndPosition& rhs)
{
  return lhs.name > rhs.name;
}

class Solver {
public:
	Solver ();
	virtual ~Solver ();
	void assign_instruction(string src, string dst, string fn_name = "");
	void binary_instruction(string dst, string op1, string op2, string operation);
	string content( string name );
	void clean_conditions_stack(string name);
	void set_sat(bool);
	bool get_fuzz_constr(string name);
	void push_condition(string condition, string function, vector<string> joints, bool fuzzme);
	string negation(string condition);
	int show_problem();
	void solve_problem();
	void free_var(string name);
	bool solvable_problem();
	bool get_is_propagated_constant(string varname);
	string gettype(string name);
	void set_name_hint(string name, string hint);
	string get_name_hint(string name);
	void set_offset_tree( string varname, string tree );
	string get_sized_type(string name);
	void dump_conditions( stringstream& sstr );
	void load_forced_free_vars();
	string get_type(string name);
	void solver_insert_sync_point(string lockunlock, string sync_name, string mutex_name);
	string realvalue_mangled(string varname);
	string realvalue(string varname);
	void settype(string name, string type);
	vector<bool> get_path_stack();
	void push_path_stack(bool step);
	void print_path_stack();
	map<string, Variable> get_map_variables();
	vector<Condition> get_stack_conditions();
	set<NameAndPosition> get_variable_names();

private:

	map<string, Variable> variables;



	void dump_conditions(FILE* file = stdout);
	void dump_variables(FILE* file = stdout);
	void dump_concurrency_constraints(FILE* file = stdout);
	void dump_check_sat(FILE* file = stdout);
	void dump_exclusions(FILE* file = stdout);
	void dump_sync_variables(FILE* file = stdout);
	void dump_header(FILE* file = stdout);
	void dump_type_limits(FILE* file = stdout);
	void dump_tail(FILE* file = stdout);
	void dump_get(FILE* file = stdout);
	void dump_get_fuzz(FILE* file = stdout);
	void dump_assigns(FILE* file = stdout);
	void flat_problem();
	void insert_variable(string name, string position);
	string extract_condition(string content);
	string get_last_condition(string name);
	string actual(string name);
	string past(string name);
	string name_without_suffix(string name);
	void dump_flatened_variables(FILE* file = stdout );
	void dump_flatened_conditions(FILE* file = stdout );
	bool check_name(string name);
	bool check_unmangled_name(string name);
	string name( string input, string fn_name = "" );
	void set_real_value(string varname, string value, string fn_name );
	void set_real_value(string varname, string value );
	string itos(int i);
	void set_fuzz_constr(string name);
	string get_offset_tree( string varname );
	bool check_mangled_name(string name);
	set<string> unlock_points(string mutex);
	string or_unlocking(string condition, string mutex);
	void substitute_locks(string& condition);
	string or_paths(string dest);
	void substitute_unlocks(string& condition);
	void substitute_paths(string& condition);
	string and_stores(string sync_point);
	void substitute_stores(string& condition);
	void substitute_conds(string& condition);
	string stack(string sync_point);
	void substitute_sync(string& condition);
	int minval(string type);
	int maxval(string type);
	int get_num_fuzzs();
	void dump_get_free(FILE* file);
	void set_real_value_mangled(string varname, string value );
	bool get_is_sat(string is_sat);
	bool get_is_sat_with_fuzz( vector<string> fuzz_constraints );
	string get_exclusion( vector<string> excluded_values );
	void insert_exclusion(string exclusion);
	void clean_exclusions();
	int get_num_fvars();
	void set_is_propagated_constant(string varname);
	bool is_constant(string varname);
	void setcontent(string varname, string content);
	bool is_forced_free(string position);
	string result_get(string get_str);
	bool implemented_operation(string operation);
	string wired_and( string op1, string op2, int nbits );
	string wired_xor( string op1, string op2, int nbits );
	vector<bool> path_stack;
};



















#endif /* end of include guard: _SOLVER_H_ */

