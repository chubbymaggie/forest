/*
 * =====================================================================================
 * /
 * |     Filename:  concurrency.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/30/2013 03:52:15 PM
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

#include "concurrency.h"

using namespace std;

extern Solver* solver;
extern Database* database;
extern Options* options;
extern Operators* operators;

Concurrency::Concurrency(){;}
Concurrency::~Concurrency(){;}

void Concurrency::insert_global_types(){
	
	set<NameAndPosition> variable_names = solver->get_variable_names();
	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = solver->get_type(it->name);

		database->insert_global_type(name, type);

	}
	
}

void Concurrency::insert_stores(string sync_name){

	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		database->insert_store(it->first, it->second, sync_name );
	}
	map_pos_to_last_store.clear();

}

void Concurrency::mutex_lock_info(char* _mutex_name, char* _sync_name){

	debug && printf("mutex_lock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	insert_stores(sync_name);
	insert_global_types();

	stringstream conds;
	solver->dump_conditions(conds);

	MutexInfo mutexinfo = {"lock", mutex_name, sync_name, conds.str()};
	mutexinfos.insert(mutexinfo);

	sync_points.insert(sync_name);

	database->insert_sync_points(sync_name, sync_points);

}

void Concurrency::mutex_unlock_info(char* _mutex_name, char* _sync_name){


	debug && printf("mutex_unlock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	insert_stores(sync_name);
	insert_global_types();

	stringstream conds;
	solver->dump_conditions(conds);

	MutexInfo mutexinfo = {"unlock", mutex_name, sync_name, conds.str()};
	mutexinfos.insert(mutexinfo);

	sync_points.insert(sync_name);

	database->insert_sync_points(sync_name, sync_points);

}

void Concurrency::dump_sync_table(){

	for( set<MutexInfo>::iterator it = mutexinfos.begin(); it != mutexinfos.end(); it++ ){
		database->database_insert_concurrency(it->lockunlock, it->mutex_name, it->sync_name, it->conds);
	}
	
}


void Concurrency::begin_concurrency(){
	options->read_options();
	debug = options->cmd_option_bool("verbose");
}


void Concurrency::end_concurrency(){
	dump_sync_table();
}

void Concurrency::update_store(string dst, string content){

	map_pos_to_last_store[dst] = content;
}


void Concurrency::mutex_lock_constraints(char* _mutex_name, char* _sync_name){

	printf("mutex_lock_constraints %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	solver->solver_insert_sync_point("lock", sync_name, mutex_name);
}

void Concurrency::mutex_unlock_constraints(char* _mutex_name, char* _sync_name){

	printf("mutex_unlock_constraints %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	solver->solver_insert_sync_point("unlock", sync_name, mutex_name);

}

#define UNDERSCORE "_"

#define name(A) operators->name(A)
#define realvalue(A) solver->realvalue(name(A))

void Concurrency::load_instr(char* _dst, char* _addr){

	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem" UNDERSCORE + realvalue(addr);


	//if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for load");
	//if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for load");

	if(options->cmd_option_bool("secuencialize")){
		database->insert_load(src);
	}

	solver->assign_instruction(name(src),name(dst));

	debug && printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(addr).c_str(),
								    name(addr).c_str(), realvalue(addr).c_str(),
								    name(src).c_str(), realvalue(src).c_str(),
							            name(dst).c_str(), realvalue(dst).c_str()
								    );
	//exit(0);

}

void Concurrency::store_instr(char* _src, char* _addr){

	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem" UNDERSCORE + realvalue(string(_addr)) ;




	//if(!check_mangled_name(name(src))) assert(0 && "Wrong src for store");
	//if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for store");
	//if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for store");


	if(options->cmd_option_bool("secuencialize")){
		solver->content(name(dst));
	
		stringstream stack;
		solver->dump_conditions(stack);
	}

	if(options->cmd_option_bool("concurrency")){
		update_store(dst, solver->content(name(src)));
	}



	solver->assign_instruction(name(src),name(dst));

	debug && printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",name(src).c_str(), name(addr).c_str(),
			                                           name(src).c_str(), realvalue(src).c_str(),
								   name(addr).c_str(), realvalue(addr).c_str(),
								   name(dst).c_str(), realvalue(dst).c_str() );

}


#undef name 
#undef realvalue

