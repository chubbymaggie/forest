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


void Z3RealInt::or_operation(string op1, string op2, string dst, stringstream& content_ss){



		if( is_constant(op2) )
			content_ss << or_constant( op1, realvalue(op2) );
		else
			assert(0 && "Non-Supported Operation");

		int op1_i = stoi(realvalue(op1));
		int op2_i = stoi(realvalue(op2));
		int res = op1_i | op2_i;
		stringstream result; result << res;
		set_real_value(dst, result.str());




}


void Z3RealInt::and_operation(string op1, string op2, string dst, stringstream& content_ss){



		if( is_constant(op2) )
			content_ss << and_constant( op1, realvalue(op2) );
		else
			assert(0 && "Non-Supported Operation");


		int op1_i = stoi(realvalue(op1));
		int op2_i = stoi(realvalue(op2));
		int res = op1_i & op2_i;
		stringstream result; result << res;
		set_real_value(dst, result.str());


}

string Z3RealInt::and_constant(string op1, string op2){

	stringstream ret;
	int op2_i = stoi(op2);
	string op2_b = binary_rep(op2_i);
	string content1 = content(op1);

	printf("and_constant %s %s %s %s\n", op1.c_str(),content1.c_str(), op2.c_str(), op2_b.c_str());


	vector<string> z_bits;

	for ( unsigned int i = 0,mult1=1,mult2=2; i < op2_b.length()-1; i++,mult1*=2, mult2*=2) {

		char bit = op2_b[op2_b.length()-i-1];

		printf("bit %c mult %d\n", bit, mult1);

		stringstream x_bit_i_sh;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i_sh << "(- (mod " << content1 << " " << mult2 << ") (mod " << content1 << " " << mult1 << "))";

		if(bit == '1'){
			z_bit_i_sh << x_bit_i_sh.str();
		} else {
			z_bit_i_sh << "";
		}


		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < z_bits.size(); i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;



	return ret.str();

}

string Z3RealInt::or_constant(string op1, string op2){

	stringstream ret;
	int op2_i = stoi(op2);
	string op2_b = binary_rep(op2_i);
	string content1 = content(op1);

	printf("or_constant %s %s %s %s\n", op1.c_str(),content1.c_str(), op2.c_str(), op2_b.c_str());


	vector<string> z_bits;

	for ( unsigned int i = 0,mult1=1,mult2=2; i < op2_b.length()-1; i++,mult1*=2, mult2*=2) {

		char bit = op2_b[op2_b.length()-i-1];

		printf("bit %c mult %d\n", bit, mult1);

		stringstream x_bit_i_sh;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i_sh << "(- (mod " << content1 << " " << mult2 << ") (mod " << content1 << " " << mult1 << "))";

		if(bit == '1'){
			z_bit_i_sh << "(- " << mult1 << " " << x_bit_i_sh.str() << ")";
		} else {
			z_bit_i_sh << "";
		}


		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < z_bits.size(); i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + content1 + " " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;



	return ret.str();

}


void Z3RealInt::xor_operation(string op1, string op2, string dst, stringstream& content_ss){


		if( is_constant(op2) && realvalue(op2) == "-1" )
			content_ss  << complement_op( op1 );
		else
			assert(0 && "Non-Supported Operation");

		if( is_constant(op2) && realvalue(op2) == "-1" ){
			int op1_i = stoi(realvalue(op1));
			int res = ~op1_i;
			stringstream result; result << res;
			set_real_value(dst, result.str());
		}

}


string Z3RealInt::complement_op(string op1){

	stringstream ret;
	string content1 = content(op1);

	printf("complement_operation %s \n", op1.c_str());

	//ret << "(ite (> " << content1 << " 0) (- (+ " << content1 << " 1)) (- -256 (+ " << content1 << " 1)))";
	//ret << "(ite (> " << content1 << " 0) (- (+ " << content1 << " 1)) (- -256 (+ " << content1 << " 2)))";
	ret << "(- (+ " << content1 << " 1))";

	return ret.str();

}

