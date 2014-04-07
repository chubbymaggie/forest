/*
 * =====================================================================================
 * /
 * |     Filename:  z3_realint.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/07/2014 09:55:29 AM
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
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

Z3RealInt::Z3RealInt(){
	
}

Z3RealInt::~Z3RealInt(){
	
}

void Z3RealInt::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-option :pp-decimal true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");

}

void Z3RealInt::dump_variables(FILE* file){

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = z3_type(get_type(it->name));

		//dump_variable(position, type, file);
		fprintf(file,"(declare-fun %s () %s)\n", position.c_str(), type.c_str());

		
	}
	

}

string Z3RealInt::name_operation(string operation){
	return operation;
}


string Z3RealInt::canonical_representation(string in){

	return in;
}

