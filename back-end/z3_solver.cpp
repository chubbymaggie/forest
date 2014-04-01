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
#include "timer.h"
#include "utils.h"

extern Options* options;
extern Operators* operators;
extern Database* database;
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




void Z3Solver::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-option :pp-decimal true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");

}


void Z3Solver::dump_variables(FILE* file){

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = z3_type(get_type(it->name));

		//dump_variable(position, type, file);
		fprintf(file,"(declare-fun %s () %s)\n", position.c_str(), type.c_str());

		
	}
	

}

void Z3Solver::dump_pivots(FILE* file){

	//printf("dump pivots\n");

	for( map<string,vector<Pivot> >::iterator it = pivot_variables.begin(); it != pivot_variables.end(); it++ ){

		vector<Pivot> pivots = it->second;

		for( vector<Pivot>::iterator it2 = pivots.begin(); it2 != pivots.end(); it2++ ){
		
			string variable = it2->variable;


			string hintpivot = variable;
			string hint = hintpivot.substr(0, hintpivot.find("_pivot_"));
			string name = find_by_name_hint(hint);
			
			//printf("gettype %s %s\n", name.c_str(), get_type(name).c_str() );
			string type = get_type(name);
			//printf("gettype\n");
			fprintf(file, "(declare-fun %s () %s)\n", name.c_str(), type.c_str() );
		}
		

	}
	
}


void Z3Solver::dump_type_limits(FILE* file){

	if(options->cmd_option_bool("unconstrained")) return;


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = get_sized_type(it->name);

		string position = it->position;

		if( get_type(it->name) != "Real" )
			fprintf(file,"(assert (and (>= %s %d) (<= %s %d)))\n", position.c_str(), minval(type), position.c_str(), maxval(type) );
		
	}
}



void Z3Solver::dump_int_constraints(FILE* file){


	for ( unsigned int i = 0; i < int_constraints.size(); i++) {
		fprintf(file, "(declare-fun int_constraint_%d () Int)\n", i);
	}

	unsigned int i = 0;
	for( set<string>::iterator it = int_constraints.begin(); it != int_constraints.end(); it++ ){
		fprintf(file, "(assert (= %s int_constraint_%d))\n", it->c_str(), i);
		i++;
	}

}


void Z3Solver::dump_conditions(FILE* file){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		fprintf(file,"(assert %s)\n", locknames(it->cond).c_str() );
	}
	
}

void Z3Solver::dump_check_sat(FILE* file){


	fprintf(file,"(check-sat)\n");

}


void Z3Solver::dump_get(FILE* file){



	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n", locknames(it->position).c_str(), it->name.c_str() );
	}
	
	fprintf(file,"; --- ↑free ↓non-free \n" );

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;
		
		//printf("----- name %s type %s\n", it->first.c_str(), gettype(it->first).c_str() );

		fprintf(file,"(get-value (%s)); %s\n", locknames(it->second.content).c_str(), it->first.c_str() );
	}

	fprintf(file,"; --- ↑non-free ↓forced_free \n" );

	//for( set<string>::iterator it = forced_free_vars.begin(); it != forced_free_vars.end(); it++ ){
		//fprintf(file,"(get-value (%s));\n", get_first_content(*it).c_str() );
	//}
	
	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		fprintf(file, "(get-value (%s)); %s\n", it->second.c_str(), it->first.c_str());
	}
	
	
	
}

void Z3Solver::dump_tail(FILE* file){

	fprintf(file,"(exit)\n");
}




