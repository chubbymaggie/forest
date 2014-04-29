/*
 * =====================================================================================
 * /
 * |     Filename:  z3_double.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/28/2014 02:15:04 PM
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


#include "z3_double.h"
#include "z3_bitvector.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"
#include "architecture.h"


extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;


Z3Double::Z3Double(){
	
}

Z3Double::~Z3Double(){
	
}

void Z3Double::dump_problem(string& filename_base){

	string filename_initial = filename_base;

	{
		vector<string> tokens = tokenize(filename_initial, ".");
		filename_base = tokens[0] + "_realint_" + ".smt2";

		FILE* file = fopen(filename_base.c_str(), "w");
		Z3RealInt::dump_header(file);
		Z3RealInt::dump_variables(file);
		//dump_extra(file);
		dump_conditions(file);
		dump_check_sat(file);
		dump_get(file);
		dump_tail(file);
		fclose(file);
	}

	{
		vector<string> tokens = tokenize(filename_initial, ".");
		filename_base = tokens[0] + "_bitvector_" + ".smt2";

		FILE* file = fopen(filename_base.c_str(), "w");
		Z3BitVector::dump_header(file);
		Z3BitVector::dump_variables(file);
		//dump_extra(file);
		dump_conditions(file);
		dump_check_sat(file);
		dump_get(file);
		dump_tail(file);
		fclose(file);
	}

}

void Z3Double::dump_header(FILE* file){

	//Z3RealInt::dump_header(file);
	//Z3BitVector::dump_header(file);

}

void Z3Double::dump_variables(FILE* file){

	//Z3RealInt::dump_variables(file);
	//Z3BitVector::dump_variables(file);
	

}

void Z3Double::right_shift(string op1, string op2, string dst, stringstream& content_ss){

	Z3RealInt::right_shift(op1, op2, dst, content_ss);
	Z3BitVector::right_shift(op1, op2, dst, content_ss);

}

void Z3Double::left_shift(string op1, string op2, string dst, stringstream& content_ss){

	Z3RealInt::left_shift(op1, op2, dst, content_ss);
	Z3BitVector::left_shift(op1, op2, dst, content_ss);

}

void Z3Double::and_operation(string op1, string op2, string dst, stringstream& content_ss){


	Z3RealInt::and_operation(op1, op2, dst, content_ss);
	Z3BitVector::and_operation(op1, op2, dst, content_ss);

}

void Z3Double::or_operation(string op1, string op2, string dst, stringstream& content_ss){

	Z3RealInt::or_operation(op1, op2, dst, content_ss);
	Z3BitVector::or_operation(op1, op2, dst, content_ss);

}

string Z3Double::canonical_representation(string in){

	Z3RealInt::canonical_representation(in);
	return Z3BitVector::canonical_representation(in);
}

string Z3Double::internal_representation(int in, string type){
	 Z3RealInt::internal_representation(in, type);
	return Z3BitVector::internal_representation(in, type);
}

string Z3Double::name_operation(string operation){
	Z3RealInt::name_operation(operation);
	return Z3BitVector::name_operation(operation);
}


void Z3Double::xor_operation(string op1, string op2, string dst, stringstream& content_ss){
	Z3RealInt::xor_operation(op1, op2, dst, content_ss);
	return Z3BitVector::xor_operation(op1, op2, dst, content_ss);
}



void Z3Double::dump_extra(FILE* file){
	Z3RealInt::dump_extra(file);
	return Z3BitVector::dump_extra(file);
}


void Z3Double::cast_instruction(string src, string dst, string type_src, string type_dst){

	Z3RealInt::cast_instruction(src, dst, type_src, type_dst);
	return Z3BitVector::cast_instruction(src, dst, type_src, type_dst);
	
}


map<set<pair<string, int> > , int > Z3Double::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){

	Z3RealInt::get_idx_val(base,idx_content,indexes, first_address, last_address);
	return Z3BitVector::get_idx_val(base,idx_content,indexes, first_address, last_address);

}

