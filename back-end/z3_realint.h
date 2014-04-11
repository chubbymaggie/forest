/*
 * =====================================================================================
 * /
 * |     Filename:  z3_realint.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/07/2014 09:55:48 AM
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

#ifndef _Z3_REALINT_H_
#define _Z3_REALINT_H_

#include "z3_solver.h"

class Z3RealInt : public Z3Solver{
public:
	Z3RealInt();
	virtual ~Z3RealInt();

	void dump_variables(FILE* file);
	void dump_header(FILE* file);

	void or_operation(string op1, string op2, string dst, stringstream& content_ss);
	void and_operation(string op1, string op2, string dst, stringstream& content_ss);
	void xor_operation(string op1, string op2, string dst, stringstream& content_ss);
	void right_shift(string op1, string op2, string dst, stringstream& content_ss);
	void left_shift(string op1, string op2, string dst, stringstream& content_ss);

private:
	string name_operation(string operation);
	string canonical_representation(string in);
	string and_constant(string op1, string op2);
	string or_constant(string op1, string op2);
	string complement_op(string op1);
	void dump_extra(FILE* file);
	void dump_type_limits(FILE* file);
	void dump_int_constraints(FILE* file);
	int minval(string type);
	int maxval(string type);
	string internal_representation(int in, string type);
	
};


#endif /* end of include guard: _Z3_REALINT_H_ */
