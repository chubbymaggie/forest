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

#define debug true

sqlite3 *db;



extern map<string, Variable> variables;
extern set<string> variable_names;
extern vector<string> conditions;


static int callback(void *NotUsed, int argc, char **argv, char **azColName){
	return 0;
}

void start_database(){
	debug && printf("\e[31m start_database \e[0m\n"); fflush(stdout);
	sqlite3_open("database.db", &db);
}

void end_database(){
	debug && printf("\e[31m end_database \e[0m\n"); fflush(stdout);
	sqlite3_close(db);
}

void drop_tables(){

	debug && printf("\e[31m drop_tables \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "drop table problems;";
	action << "drop table variables;";
	action << "drop table results;";


	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void create_tables(){

	drop_tables();

	debug && printf("\e[31m create_tables \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "create table problems(";
	action << "problem_id INTEGER PRIMARY KEY AUTOINCREMENT,";
	action << "sat bool";
	action << ");";


	action << "create table variables(";
	action << "name varchar(50),";
	action << "type varchar(50),";
	action << "problem_id INTEGER";
	action << ");";

	action << "create table results(";
	action << "name varchar(50),";
	action << "value varchar(50),";
	action << "name_hint varchar(50),";
	action << "is_memory bool,";
	action << "problem_id INTEGER";
	action << ");";


	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	debug && printf("\e[31m end_tables \e[0m\n"); fflush(stdout);
}

void insert_problem(){

	stringstream action;
	string id = "(select max(problem_id) from problems)";

	action << "insert into problems (sat) values (" << (solvable_problem()?1:0) << ");";

	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
		string name = *it;
		string type = get_type(name);
		action << "insert into variables values ('" << name << "','" << type << "'," << id << ");";
	}
	
	if( solvable_problem() ){
		get_values();


		for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
			string name = *it;
			string value = realvalue(name);
			string hint = variables[name].name_hint;
			bool is_memory = (name.substr(0,4) == "mem_");
			action << "insert into results values ('" << name << "','" << value << "','" << hint << "'," << is_memory << "," << id << ");";

		}

		//for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

			//if( it->second.content == "") continue;
			//string name = it->first;
			//string value = realvalue(name);
			//string hint = variables[name].name_hint;
			//bool is_memory = (name.substr(0,4) == "mem_");
			//action << "insert into results values ('" << name << "','" << value << "','" << hint << "'," << is_memory << "," << id << ");";
			
		//}
		
		

		
	}

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

