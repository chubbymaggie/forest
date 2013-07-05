/*
 * =====================================================================================
 * /
 * |     Filename:  database_measurement.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 11:54:25 AM
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


#include "database_measurement.h"

extern vector<bool> path_stack;

#define debug true

sqlite3 *db;


vector< pair<string, string> > retsqlite;


void start_database(){
	debug && printf("\e[31m start_database \e[0m\n"); fflush(stdout);
	sqlite3_open("database.db", &db);
}

void end_database(){
	debug && printf("\e[31m end_database \e[0m\n"); fflush(stdout);
	sqlite3_close(db);
}

static int callback(void *NotUsed, int argc, char **argv, char **azColName){



	for(int i=0; i<argc; i++){
		string name = string(azColName[i] );
		string value = string(argv[i]);
		retsqlite.push_back( pair<string, string>(name, value) );
	}

	return 0;
}

void insert_measurement(string name, string value){

	stringstream action;

	action << "insert into measurements values ('" << name << "','" << value << "');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );


}

void insert_problem(){

	stringstream action;
	//string id = "(select max(problem_id) from problems)";
	string id = "(select count() from problems)";

	string path;
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		path += (*it)?"T":"F";
	}
	
	action << "insert into problems (path) values (" << "'" << path << "');";

	printf("action %s\n", action.str().c_str() );

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}
