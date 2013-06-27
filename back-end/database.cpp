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

#define debug false

sqlite3 *db;


extern map<string, Variable> variables;
extern set<NameAndPosition> variable_names;
extern vector<string> conditions;
extern vector<bool> path_stack;

vector< pair<string, string> > retsqlite;

static int callback(void *NotUsed, int argc, char **argv, char **azColName){



	for(int i=0; i<argc; i++){
		string name = string(azColName[i] );
		string value = string(argv[i]);
		retsqlite.push_back( pair<string, string>(name, value) );
	}

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
	action << "drop table measurements;";


	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void create_tables(){

	drop_tables();

	debug && printf("\e[31m create_tables \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "create table problems(";
	action << "problem_id INTEGER PRIMARY KEY AUTOINCREMENT,";
	action << "sat bool,";
	action << "path varchar(50)";
	action << ");";


	action << "create table variables(";
	action << "name varchar(50),";
	action << "type varchar(50),";
	action << "position varchar(50),";
	action << "problem_id INTEGER";
	action << ");";

	action << "create table results(";
	action << "name varchar(50),";
	action << "value varchar(50),";
	action << "name_hint varchar(50),";
	action << "is_free bool,";
	action << "problem_id INTEGER";
	action << ");";

	action << "create table measurements(";
	action << "key varchar(50),";
	action << "value varchar(50)";
	action << ");";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	debug && printf("\e[31m end_tables \e[0m\n"); fflush(stdout);
}

void insert_problem(){

	stringstream action;
	//string id = "(select max(problem_id) from problems)";
	string id = "(select count() from problems)";

	string path;
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		path += (*it)?"T":"F";
	}
	
	action << "insert into problems (sat, path) values (" << (solvable_problem()?1:0) << ",'" << path << "');";

	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
		string name = it->name;
		string type = get_type(name);
		string position = it->position;
		action << "insert into variables values ('" << name << "','" << type << "','" << position << "'," << id << ");";
	}
	
	if( solvable_problem() ){
		//get_values();


		for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
			string name = it->name;
			string value = (variables[name].real_value == "")?string("0"):variables[name].real_value;
			//string value = variables[name].real_value;
			string hint = variables[name].name_hint;

			action << "insert into results values ('" << name << "','" << value << "','" << hint << "'," << 1 << "," << id << ");";
			debug && printf("\e[31m insert_result \e[0m name %s value %s\n", name.c_str(), value.c_str());

		}

		for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

			if( it->second.content == "" ) continue;

			string name = it->first;
			string value = realvalue(name);
			string hint = variables[name].name_hint;

			action << "insert into results values ('" << name << "','" << value << "','" << hint << "'," << 0 << "," << id << ");";
			//printf("%s\n", value.c_str());

			//printf("%s\n", action.str().c_str() );

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

bool yet_covered(){



	string path;
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		path += (*it)?"T":"F";
	}

	stringstream action;
	action << "select * from problems where path='" << path << "';";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	return retsqlite.size();

}



void insert_measurement(string name, string value){

	stringstream action;

	action << "insert into measurements values ('" << name << "','" << value << "');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}



