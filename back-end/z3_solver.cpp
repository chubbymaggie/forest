/*
 * =====================================================================================
 * /
 * |     Filename:  solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/31/2014 02:52:31 PM
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

#include "z3_solver.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "concurrency.h"
#include "timer.h"

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Concurrency* concurrency;
extern Timer* timer;

Z3Solver::Z3Solver(){
	
}

Z3Solver::~Z3Solver(){
	
}


void Z3Solver::solve_problem(){

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
	//concurrency->dump_remaining_variables(free_variables, file);
	dump_type_limits(file);
	dump_int_constraints(file);
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
		string value = result_get(*it_ret);
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
		string value = result_get(*it_ret);


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);
		//variables[name].real_value = value;

		it_ret++;
	}


	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		set_first_content_value(it->first, result_get(*it_ret));

		it_ret++;
	}
	timer->end_timer("get_values");

	timer->end_timer("solver");
}




