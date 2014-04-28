/*
 * =====================================================================================
 * /
 * |     Filename:  z3_double.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/28/2014 02:14:07 PM
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

#include "z3_realint.h"
#include "z3_bitvector.h"

class Z3Double : public Z3RealInt, public Z3BitVector {
public:
	Z3Double ();
	virtual ~Z3Double ();


	string canonical_representation(string in);
	void cast_instruction(string src, string dst, string type_src, string type_dst);
	map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address);


private:
	string name_operation(string operation);
	string internal_representation(int in, string type);
	void or_operation(string op1, string op2, string dst, stringstream& content_ss);
	void and_operation(string op1, string op2, string dst, stringstream& content_ss);
	void xor_operation(string op1, string op2, string dst, stringstream& content_ss);
	void left_shift(string op1, string op2, string dst, stringstream& content_ss);
	void right_shift(string op1, string op2, string dst, stringstream& content_ss);
	void dump_header(FILE* file);
	void dump_variables(FILE* file);
	void dump_extra(FILE* file);










};
