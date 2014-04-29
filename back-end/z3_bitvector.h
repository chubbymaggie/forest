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

class Z3BitVector : virtual public Z3Solver{
public:
	Z3BitVector ();
	virtual ~Z3BitVector ();

	string canonical_representation(string in);
	void cast_instruction(string src, string dst, string type_src, string type_dst);
	map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address);
	string internal_condition(string condition);

protected:
	void dump_problem(string& filename_base);
	string internal_representation(int in, string type);
	void dump_variables(FILE* file);
	void dump_extra(FILE* file);
	void dump_header(FILE* file);
	
};


#endif /* end of include guard: _Z3_BITVECTOR_H_ */


