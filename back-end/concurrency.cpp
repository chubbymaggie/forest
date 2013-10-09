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

void mutex_lock(char* _mutex_name, char* _sync_name){

	printf("mutex_lock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

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

	printf("mutex_unlock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

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



