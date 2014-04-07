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

void Z3BitVector::solve_problem(){

	if(options->cmd_option_str("max_depth") != "" && conditions.size()-1 > options->cmd_option_int("max_depth")){
		sat = 0;
		return;
	}

	timer->start_timer();

	vector<string> ret_vector;

	sat = 0;

	stringstream filename;
	filename << "z3_" << rand() << ".smt2";




	options->read_options();

	timer->start_timer();
	FILE* file = fopen(filename.str().c_str(), "w");
	dump_header(file);
	dump_variables(file);
	dump_pivots(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_get(file);
	dump_tail(file);
	fclose(file);
	timer->end_timer("dump");

	debug && printf("\e[31m filename solve problem \e[0m %s\n", filename.str().c_str() );

	if(options->cmd_option_bool("see_each_problem"))
		getchar();



	FILE *fp;
	stringstream command;

	command << "z3 " << filename.str();
	command << " > /tmp/z3_output";


struct timespec ping_time;
struct timespec pong_time;
clock_gettime(CLOCK_MONOTONIC, &ping_time);


	system(command.str().c_str());

clock_gettime(CLOCK_MONOTONIC, &pong_time);
spent_time = 0;
spent_time += pong_time.tv_sec - ping_time.tv_sec;
spent_time *= 1e9;
spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
spent_time /= 1e6;




	ifstream input("/tmp/z3_output");
	string line;
	
	while( getline( input, line ) ) {
		ret_vector.push_back(line);
	}
	
	string         sat_str       = ret_vector[0];

	if(sat_str.find("error") != string::npos ){
		printf("error_in_z3\n");
		assert(0 && "Error in z3 execution");
	}
	if(sat_str.find("unknown") != string::npos )
		printf("Warning: unknown sat\n");

	sat = get_is_sat(sat_str);

	debug && printf("\e[31m problem solved \e[0m\n" );

	if(!sat){
		timer->end_timer("solver");
		return;
	}


	bool sat = 0;


	vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	set<NameAndPosition> free_variables_aux;

	timer->start_timer();
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++,it_ret++ ){

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string varname = it->name;
		string value = canonical_representation(result_get(*it_ret));
		string hint = it->position;


		debug && printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);

		NameAndPosition nandp = {varname, hint, value};
		free_variables_aux.insert(nandp);
		//it->value = value;
		//set_real_value_hint(hint, value);
		//variables[varname].real_value = value;

	}

	free_variables = free_variables_aux;


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string name = it->first;
		string value = canonical_representation(result_get(*it_ret));


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);
		//variables[name].real_value = value;

		it_ret++;
	}


	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		set_first_content_value(it->first, canonical_representation(result_get(*it_ret)));

		it_ret++;
	}
	timer->end_timer("get_values");

	timer->end_timer("solver");
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

		printf("dump_variables_type %s\n", type.c_str());

		if(type == "IntegerTyID32")
			bits = 32;
		else
			assert(0 && "Unknown Type");

		//dump_variable(position, type, file);
		fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);

		
	}
	

}

void Z3BitVector::right_shift(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(bvshr " << content(op1) << " " << content(op2) << ")";

		int places = stoi( canonical_representation(op2) );

		int result_i = stoi(canonical_representation(realvalue(op1))) >> places;

		stringstream result; result << internal_representation(result_i);
		set_real_value(dst, result.str());

}

void Z3BitVector::left_shift(string op1, string op2, string dst, stringstream& content_ss){



		content_ss << "(bvshl " << content(op1) << " " << content(op2) << ")";

		int places = stoi( canonical_representation(op2) );

		int result_i = stoi(canonical_representation(realvalue(op1))) << places;

		stringstream result; result << internal_representation(result_i);
		set_real_value(dst, result.str());


}

void Z3BitVector::and_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvand " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(canonical_representation(realvalue(op1))) && stoi(canonical_representation(realvalue(op2)));

		stringstream result; result << internal_representation(result_i);
		set_real_value(dst, result.str());

}

void Z3BitVector::or_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvor " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(canonical_representation(realvalue(op1))) && stoi(canonical_representation(realvalue(op2)));

		stringstream result; result << internal_representation(result_i);
		set_real_value(dst, result.str());

}

string Z3BitVector::canonical_representation(string in){

	if(in == "false") return "false";
	if(in == "true") return "true";

	int a;
	char ret_str[10];
	sscanf(in.substr(2).c_str(), "%x", &a);
	sprintf(ret_str, "%d", a);

	//printf("canonical_representation in %s a %d ret %s\n", in.c_str(), a, ret_str );

	return string(ret_str);
}

string Z3BitVector::internal_representation(int in){
	char b[10];
	sprintf(b, "%02x", in);

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

		int result_i = stoi(canonical_representation(realvalue(op1))) && stoi(canonical_representation(realvalue(op2)));

		stringstream result; result << internal_representation(result_i);
		set_real_value(dst, result.str());

}

