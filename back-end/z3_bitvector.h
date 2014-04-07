/*
 * =====================================================================================
 * /
 * |     Filename:  z3_bitvector.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/02/2014 09:31:28 AM
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


#ifndef _Z3_BITVECTOR_H_
#define _Z3_BITVECTOR_H_

#include "z3_solver.h"

class Z3BitVector : public Z3Solver{
public:
	Z3BitVector ();
	virtual ~Z3BitVector ();

	void solve_problem();
	string canonical_representation(string in);

private:
	string name_operation(string operation);
	string internal_representation(int in);
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
	bool need_for_dump(string name, string content);
	void dump_tail(FILE* file);
	void dump_get(FILE* file);
	void dump_check_sat(FILE* file);
	void dump_conditions(FILE* file);
	void dump_pivots(FILE* file);
	void dump_header(FILE* file);
	void dump_variables(FILE* file);
	
};


#endif /* end of include guard: _Z3_BITVECTOR_H_ */


