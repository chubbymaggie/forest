/*
 * =====================================================================================
 * /
 * |     Filename:  solver_wrapper.h
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

#ifndef _SOLVER_WRAPPER_H_
#define _SOLVER_WRAPPER_H_

#include <stdio.h>
#include <string>
#include <string.h>
#include <set>
#include <map>
#include <vector>


using namespace std;



typedef struct Condition {
	string cond;
	string function;
	set<string> joints;
} Condition;



typedef struct Variable {
	string real_value;
	string type;
	string name_hint;
	string content;
	string tree;
	int first_address;
	int last_address;
	bool is_propagated_constant;
	bool comes_from_non_annotated;
	map<set<pair<string, int> > , int > idx_values;
	set<string> indexes;
	bool outofbounds;
} Variable;


typedef struct NameAndPosition {
	string name;
	string position;
	string value;
} NameAndPosition;


typedef struct Pivot {
	string variable;
	string function;
} Pivot;


inline bool operator<(const NameAndPosition& lhs, const NameAndPosition& rhs)
{
  //return (lhs.name + lhs.position) > (rhs.name + rhs.position);
  return lhs.position > rhs.position;
}

class  SolverWrapper{
public:
	virtual void assign_instruction(string src, string dst, string fn_name = "") = 0;
	virtual void binary_instruction(string dst, string op1, string op2, string operation) = 0;
	virtual void solve_problem() = 0;

	virtual ~SolverWrapper ();
	float get_solve_time();
	void add_int_constraint(string src);
	void set_outofbounds(string varname, bool outofbounds = true);
	bool get_outofbounds(string varname);
	void store_idx_vals(string dst, map<set<pair<string, int> > , int > map_idx_val);
	void sym_store(string src, string addr);
	void sym_load(string dst, string idx_content);
	void push_condition_static(string cond, bool invert);
	void load_state();
	void save_state();
	void push_condition(string name, string actual_function, vector<string> joints, bool invert);
	string get_comma_stack_conditions_static();
	string get_path_stack_str();
	void variable_store(string src,string idx_content, int first_address, int last_address );
	void pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base);
	void dump_model();
	void set_content(string name, string content);
	void clean_pivots();
	void push_condition(string cond, bool invert = false );
	bool get_comes_from_non_annotated(string name);
	void set_comes_from_non_annotated(string name);
	int get_last_address(string name);
	void set_last_address(string name, int last_address);
	int get_first_address(string name);
	void set_first_address(string name, int first_address);
	string get_first_content_value(string var);
	void pivot_hint(string hint, string name);
	void dump_variable(string name, string type, FILE* file);
	void pivot_variable(string variable, string name);
	SolverWrapper ();
	string content( string name );
	void clean_conditions_stack(string name);
	void set_sat(bool);
	void push_condition(string condition, string function, vector<string> joints);
	string negation(string condition);
	int show_problem();
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
	set<NameAndPosition> get_free_variables();
	string get_position(string name);
	string find_by_name_hint(string hint);
	void setcontent(string varname, string content);
	bool is_forced_free(string position, bool colateral_effect = true);
	void insert_variable(string name, string position);
	bool is_constant(string varname);
	string get_comma_stack_conditions();
	void set_is_propagated_constant(string varname);
	void unset_is_propagated_constant(string varname);

protected:
	vector<int> jump_offsets(string offset_tree);
	set<set<pair<string, int> > > get_exclusions( map<set<pair<string, int> > , int > solutions );
	vector<bool> path_stack_save;
	vector<string> conditions_static_save;
	vector<Condition> conditions_save;

	bool sat;
	float spent_time;
	void check_name_and_pos(string name, string position);
	string z3_type(string type);
	set<string> int_constraints;
	bool is_free_var(string name);
	void init_indexes(string dst, string op1, string op2 = "");
	bool is_free_var_by_position(string position);
	void add_indexes(string dst, vector<string> indexes);
	string get_idx_type(string idx_content );
	void load_idx_vals(string dst, map<set<pair<string, int> > , int > map_idx_val);
	void add_range_index(string dst, map<set<pair<string, int> > , int > map_idx_val );
	map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address);
	string negateop(string predicate);
	bool need_for_dump(string name, string content);
	string get_anded_stack_conditions();
	void set_real_value_hint(string hint, string value );
	string complement_op(string op1);
	//void propagate_unary(string src, string dst);
	void propagate_unary(string src, string dst, bool forcedfree);
	void propagate_binary(string op1, string op2, string dst);
	void set_first_content_value(string var, string value);
	string get_first_content(string src);
	void set_first_content(string src, string content);
	bool is_pivot(string src);
	void substitute_pivots(string& src);
	set<string> already_forced_free;

	map<string, string> stacks;
	map<string, Variable> variables;
	set<NameAndPosition> free_variables;
	vector<string> flatened_conditions;
	set<string> flatened_variables;
	vector<Condition> conditions;
	vector<string> conditions_static;
	set<string> forced_free_vars;
	map<string, vector<Pivot> > pivot_variables;
	map<string, string> first_content;
	map<string, string> first_content_value;


	void show_conditions();
	void show_variables();
	void show_concurrency_constraints();
	void show_check_sat();
	void show_header();
	void show_type_limits();
	void show_tail();
	void show_get();
	void show_int_constraints();
	void show_assigns();
	void show_pivots();
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
	string get_offset_tree( string varname );
	bool check_mangled_name(string name);
	set<string> unlock_points(string mutex);
	string or_unlocking(string condition, string mutex);
	string or_paths(string dest);
	string and_stores(string sync_point);
	string stack(string sync_point);
	int minval(string type);
	int maxval(string type);
	void set_real_value_mangled(string varname, string value );
	bool get_is_sat(string is_sat);
	int get_num_fvars();
	string result_get(string get_str);
	bool implemented_operation(string operation);
	string wired_and( string op1, string op2, int nbits );
	string wired_xor( string op1, string op2, int nbits );
	vector<bool> path_stack;
	string find_mem_of_id(string id);

	bool debug;
};

#endif /* end of include guard: _SOLVER_H_ */

