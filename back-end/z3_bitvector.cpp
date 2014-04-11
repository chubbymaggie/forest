/*
 * =====================================================================================
 * /
 * |     Filename:  z3_bitvector.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/02/2014 09:30:47 AM
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


#include "z3_bitvector.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

Z3BitVector::Z3BitVector(){
	
}

Z3BitVector::~Z3BitVector(){
	
}


void Z3BitVector::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");

}

void Z3BitVector::dump_variables(FILE* file){

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = gettype(it->name);
		int bits;

		//printf("dump_variables_type %s\n", type.c_str());

		if(type == "IntegerTyID32")
			bits = 32;
		else if(type == "IntegerTyID16")
			bits = 16;
		else if(type == "IntegerTyID8")
			bits = 8;
		else
			assert(0 && "Unknown Type");

		//dump_variable(position, type, file);
		fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);

		
	}
	

}

void Z3BitVector::right_shift(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(bvlshr " << content(op1) << " " << content(op2) << ")";

		int places = stoi( realvalue(op2) );

		int result_i = stoi(realvalue(op1)) >> places;

		stringstream result; result << internal_representation(result_i, gettype(op1));
		set_real_value(dst, result.str());

}

void Z3BitVector::left_shift(string op1, string op2, string dst, stringstream& content_ss){



		content_ss << "(bvshl " << content(op1) << " " << content(op2) << ")";

		int places = stoi( realvalue(op2) );

		int result_i = stoi(realvalue(op1)) << places;

		stringstream result; result << internal_representation(result_i, gettype(op1));
		set_real_value(dst, result.str());


}

void Z3BitVector::and_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvand " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) & stoi(realvalue(op2));

		stringstream result; result << internal_representation(result_i, gettype(op1));
		set_real_value(dst, result.str());

}

void Z3BitVector::or_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvor " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) | stoi(realvalue(op2));

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}

string Z3BitVector::canonical_representation(string in){

	// printf("canonical_representation in %s\n", in.c_str() ); fflush(stdout);
	if(in[0] != '#' && in != "true" && in != "false")
		assert(0 && "Canonical_Representation of a non-internal");


	if(in == "false") return "false";
	if(in == "true") return "true";

	int a;
	char ret_str[10];
	sscanf(in.substr(2).c_str(), "%x", &a);
	sprintf(ret_str, "%d", a);

	//printf("canonical_representation in %s a %d ret %s\n", in.c_str(), a, ret_str );

	return string(ret_str);
}

string Z3BitVector::internal_representation(int in, string type){
	char b[20];
	//printf("internal_representation_type %s\n", type.c_str());

	if(type == "IntegerTyID32")
		sprintf(b, "%08x", in);
	else if(type == "Int")
		sprintf(b, "%08x", in);
	else if(type == "IntegerTyID16")
		sprintf(b, "%04x", in);
	else if(type == "IntegerTyID8")
		sprintf(b, "%02x", in);
	else if(type == "PointerTyID")
		sprintf(b, "%08x", in);
	else
		assert(0 && "Unknown type");

	//printf("internal representation in %s a %d b %s\n", in.c_str(), a, b);
	return "#x" + string(b);
}

string Z3BitVector::name_operation(string operation){
	if(operation == "*") return "bvmul";
	if(operation == "+") return "bvadd";
	if(operation == "-") return "bvsub";
	if(operation == "/") return "bvdiv";

	assert(0 && "Unknown operation");
}


void Z3BitVector::xor_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvxor " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) && stoi(realvalue(op2));

		stringstream result; result << internal_representation(result_i, gettype(op1));
		set_real_value(dst, result.str());

}



void Z3BitVector::dump_extra(FILE* file){
}
