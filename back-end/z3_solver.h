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


#ifndef _Z3SOLVER_H_
#define _Z3SOLVER_H_

#include "solver.h"


class Z3Solver : public Solver {
public:
	void assign_instruction(string src, string dst, string fn_name = "");
	void binary_instruction(string dst, string op1, string op2, string operation);
	Z3Solver ();
	virtual ~Z3Solver ();
	void solve_problem();
	virtual void dump_variables(FILE* file) = 0;
	string z3_type(string type);
	virtual string canonical_representation(string in) = 0;
	virtual void cast_instruction(string src, string dst, string type_src, string type_dst) = 0;

protected:
	virtual string internal_representation(int in, string type) = 0;
	virtual void xor_operation(string op1, string op2, string dst, stringstream& content_ss) = 0;
	virtual void or_operation(string op1, string op2, string dst, stringstream& content_ss) = 0;
	virtual void and_operation(string op1, string op2, string dst, stringstream& content_ss) = 0;
	virtual void left_shift(string op1, string op2, string dst, stringstream& content_ss) = 0;
	virtual void right_shift(string op1, string op2, string dst, stringstream& content_ss) = 0;
	virtual void dump_extra(FILE* file) = 0;
	virtual void dump_header(FILE* file) = 0;
	virtual string name_operation(string operation) = 0;

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
	void rem_operator(string op1, string op2, string dst, stringstream& content_ss);
	void neq_operation(string op1, string op2, string dst, stringstream& content_ss);
	bool need_for_dump(string name, string content);
	void dump_tail(FILE* file);
	void dump_get(FILE* file);
	void dump_check_sat(FILE* file);
	void dump_conditions(FILE* file);
	
};

#endif /* end of include guard: _Z3SOLVER_H_ */
