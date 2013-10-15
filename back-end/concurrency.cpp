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

void Concurrency::mutex_lock(char* _mutex_name, char* _sync_name){

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

void Concurrency::mutex_unlock(char* _mutex_name, char* _sync_name){


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


