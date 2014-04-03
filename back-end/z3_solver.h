/*
 * =====================================================================================
 * /
 * |     Filename:  solver.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/31/2014 02:52:46 PM
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

#include "solver_wrapper.h"


class Z3Solver : public SolverWrapper {
public:
	void assign_instruction(string src, string dst, string fn_name = "");
	void binary_instruction(string dst, string op1, string op2, string operation);
	Z3Solver ();
	virtual ~Z3Solver ();
	void solve_problem();
	string internal_representation(string in);

private:
	void div_operation(string op1, string op2, string dst, stringstream& content_ss);
	void mul_operation(string op1, string op2, string dst, stringstream& content_ss);
	void sub_operation(string op1, string op2, string dst, stringstream& content_ss);
	void add_operation(string op1, string op2, string dst, stringstream& content_ss);
	void eq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void bt_operation(string op1, string op2, string dst, stringstream& content_ss);
	void lt_operation(string op1, string op2, string dst, stringstream& content_ss);
	void geq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void uleq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void leq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void xor_operation(string op1, string op2, string dst, stringstream& content_ss);
	void or_operation(string op1, string op2, string dst, stringstream& content_ss);
	void and_operation(string op1, string op2, string dst, stringstream& content_ss);
	void left_shift(string op1, string op2, string dst, stringstream& content_ss);
	void right_shift(string op1, string op2, string dst, stringstream& content_ss);
	void rem_operator(string op1, string op2, string dst, stringstream& content_ss);
	void neq_operation(string op1, string op2, string dst, stringstream& content_ss);
	string complement_op(string op1);
	bool need_for_dump(string name, string content);
	int minval(string type);
	int maxval(string type);
	string z3_type(string type);
	void dump_tail(FILE* file);
	void dump_get(FILE* file);
	void dump_check_sat(FILE* file);
	void dump_conditions(FILE* file);
	void dump_int_constraints(FILE* file);
	void dump_type_limits(FILE* file);
	void dump_pivots(FILE* file);
	void dump_variables(FILE* file);
	void dump_header(FILE* file);
	string and_constant(string op1, string op2);
	string or_constant(string op1, string op2);
	
};

#endif /* end of include guard: _SOLVER_H_ */
