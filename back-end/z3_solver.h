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

private:
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
