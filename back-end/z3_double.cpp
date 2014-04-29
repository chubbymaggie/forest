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
		Z3RealInt::dump_extra(file);
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
		dump_conditions(file);
		dump_check_sat(file);
		dump_get(file);
		dump_tail(file);
		fclose(file);
	}

}

void Z3Double::dump_header(FILE* file){
}

void Z3Double::dump_variables(FILE* file){
}

string Z3Double::canonical_representation(string in){
	return Z3BitVector::canonical_representation(in);
}

string Z3Double::internal_representation(int in, string type){
	return Z3BitVector::internal_representation(in, type);
}

void Z3Double::dump_extra(FILE* file){
}


void Z3Double::cast_instruction(string src, string dst, string type_src, string type_dst){
	return Z3BitVector::cast_instruction(src, dst, type_src, type_dst);
}


map<set<pair<string, int> > , int > Z3Double::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){
	return Z3BitVector::get_idx_val(base,idx_content,indexes, first_address, last_address);

}



string Z3Double::internal_condition(string condition){

	return condition;

}
