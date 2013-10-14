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

set<string> sync_points;

map<string, string> map_pos_to_last_store;

extern set<NameAndPosition> variable_names;

Concurrency::Concurrency(){;}
Concurrency::~Concurrency(){;}

void Concurrency::insert_global_types(){
	
	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = solver->get_type(it->name);

		database->insert_global_type(name, type);

		//fprintf(file,"(declare-fun %s () %s)\n", tokens[0].c_str(), type.c_str());
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}
	
}

void Concurrency::mutex_lock(char* _mutex_name, char* _sync_name){

	printf("mutex_lock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		printf("%s %s\n", it->first.c_str(), it->second.c_str());
		database->insert_store(it->first, it->second, sync_name );
	}
	map_pos_to_last_store.clear();

	insert_global_types();


	stringstream conds;
	solver->dump_conditions(conds);
	printf("-----------------------------------\n");
	//dump_conditions();
	printf("conds %s\n", conds.str().c_str() );
	printf("-----------------------------------\n");

	MutexInfo mutexinfo = {"lock", mutex_name, sync_name, conds.str()};

	mutexinfos.insert(mutexinfo);

	sync_points.insert(sync_name);

	database->insert_sync_points(sync_name, sync_points);

}

void Concurrency::mutex_unlock(char* _mutex_name, char* _sync_name){


	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		printf("%s %s\n", it->first.c_str(), it->second.c_str());
	}


	printf("mutex_unlock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);


	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		printf("%s %s\n", it->first.c_str(), it->second.c_str());
		database->insert_store(it->first, it->second, sync_name );
	}
	map_pos_to_last_store.clear();

	insert_global_types();


	stringstream conds;
	solver->dump_conditions(conds);
	printf("-----------------------------------\n");
	//dump_conditions();
	printf("conds %s\n", conds.str().c_str() );
	printf("-----------------------------------\n");

	MutexInfo mutexinfo = {"unlock", mutex_name, sync_name, conds.str()};

	mutexinfos.insert(mutexinfo);

	sync_points.insert(sync_name);

	database->insert_sync_points(sync_name, sync_points);

}

void Concurrency::dump_sync_table(){

	for( set<MutexInfo>::iterator it = mutexinfos.begin(); it != mutexinfos.end(); it++ ){
		//string lockunlock = it->lockunlock;
		//string mutex_name = it->mutex_name;
		//printf("mutex_to_insert %s %s\n", lockunlock.c_str(), mutex_name.c_str());
		database->database_insert_concurrency(it->lockunlock, it->mutex_name, it->sync_name, it->conds);
	}
	
}


void Concurrency::begin_concurrency(){
	//drop_concurrency_tables();
	//create_concurrency_tables();
}


void Concurrency::end_concurrency(){
	dump_sync_table();
}



