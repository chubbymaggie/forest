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

#include "solver_wrapper.h"

class Z3BitVector : public SolverWrapper {
public:
	Z3BitVector ();
	virtual ~Z3BitVector ();

	void assign_instruction(string src, string dst, string fn_name = "");
	void binary_instruction(string dst, string op1, string op2, string operation);
	void solve_problem();

private:
	bool need_for_dump(string name, string content);
	void dump_tail(FILE* file);
	void dump_get(FILE* file);
	void dump_check_sat(FILE* file);
	void dump_conditions(FILE* file);
	void dump_pivots(FILE* file);
	void dump_variables(FILE* file);
	void dump_header(FILE* file);
	
};


#endif /* end of include guard: _Z3_BITVECTOR_H_ */


