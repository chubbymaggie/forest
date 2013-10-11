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

#include <stdio.h>
#include "concurrency.h"
#include "database.h"
#include "solver.h"
#include <sstream>

using namespace std;

set<string> sync_points;

extern map<string, string> map_pos_to_last_store;

extern set<NameAndPosition> variable_names;

void insert_global_types(){
	
	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = get_type(it->name);

		insert_global_type(name, type);

		//fprintf(file,"(declare-fun %s () %s)\n", tokens[0].c_str(), type.c_str());
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}
	
}

void mutex_lock(char* _mutex_name, char* _sync_name){

	printf("mutex_lock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		printf("%s %s\n", it->first.c_str(), it->second.c_str());
		insert_store(it->first, it->second, sync_name );
	}
	map_pos_to_last_store.clear();

	insert_global_types();


	stringstream conds;
	dump_conditions(conds);
	printf("-----------------------------------\n");
	//dump_conditions();
	printf("conds %s\n", conds.str().c_str() );
	printf("-----------------------------------\n");

	database_insert_concurrency("lock", mutex_name, sync_name, conds.str());

	sync_points.insert(sync_name);

	insert_sync_points(sync_name, sync_points);

}

void mutex_unlock(char* _mutex_name, char* _sync_name){


	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		printf("%s %s\n", it->first.c_str(), it->second.c_str());
	}


	printf("mutex_unlock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);


	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		printf("%s %s\n", it->first.c_str(), it->second.c_str());
		insert_store(it->first, it->second, sync_name );
	}
	map_pos_to_last_store.clear();

	insert_global_types();


	stringstream conds;
	dump_conditions(conds);
	printf("-----------------------------------\n");
	//dump_conditions();
	printf("conds %s\n", conds.str().c_str() );
	printf("-----------------------------------\n");

	database_insert_concurrency("unlock", mutex_name, sync_name, conds.str());

	sync_points.insert(sync_name);

	insert_sync_points(sync_name, sync_points);

}

void begin_concurrency(){
	//drop_concurrency_tables();
	//create_concurrency_tables();
}


void mutex_lock_2(char* _mutex_name, char* _sync_name){

	printf("mutex_lock_2 %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	solver_insert_sync_point("lock", sync_name, mutex_name);
}

void mutex_unlock_2(char* _mutex_name, char* _sync_name){

	printf("mutex_unlock_2 %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	solver_insert_sync_point("unlock", sync_name, mutex_name);

}



