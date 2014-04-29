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

class Z3RealInt : virtual public Z3Solver{
public:
	Z3RealInt();
	virtual ~Z3RealInt();

	void dump_variables(FILE* file);
	void dump_header(FILE* file);

	string internal_condition(string condition);
	void cast_instruction(string src, string dst, string type_src, string type_dst);
	map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address);

protected:
	void dump_problem(string& filename_base);
	string canonical_representation(string in);
	string and_constant(string op1, string op2);
	string or_constant(string op1, string op2);
	string complement_op(string op1);
	void dump_extra(FILE* file);
	void dump_type_limits(FILE* file);
	int minval(string type);
	int maxval(string type);
	string internal_representation(int in, string type);
	
};


#endif /* end of include guard: _Z3_REALINT_H_ */
