/*
 * =====================================================================================
 * /
 * |     Filename:  database.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/13/2013 09:40:22 AM
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

#include "database.h"

sqlite3 *db;

static int callback(void *NotUsed, int argc, char **argv, char **azColName){
	return 0;
}


void start_database(){
	sqlite3_open("database.db", &db);
}

void end_database(){
	sqlite3_close(db);
}


void create_database(){

	stringstream action;
	action << "create table problems(";
	action << "problem_id Int,";
	action << "sat Bool;";
	action << ");";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
}


