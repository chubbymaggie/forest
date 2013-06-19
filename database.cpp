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
extern set<string> variable_names;
extern vector<string> conditions;


static int callback(void *NotUsed, int argc, char **argv, char **azColName){
	return 0;
}

void start_database(){
	debug && printf("start_database\n"); fflush(stdout);
	sqlite3_open("database.db", &db);
}

void end_database(){
	debug && printf("end_database\n"); fflush(stdout);
	sqlite3_close(db);
}

void drop_tables(){

	stringstream action;
	action << "drop table problems;";
	action << "drop table variables;";
	action << "drop table assigns;";
	action << "drop table operations;";
	action << "drop table results;";


	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void create_tables(){

	drop_tables();

	debug && printf("create_tables\n"); fflush(stdout);

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

	action << "create table assigns(";
	action << "dst varchar(50),";
	action << "src varchar(50),";
	action << "problem_id INTEGER";
	action << ");";

	action << "create table operations(";
	action << "dst varchar(50),";
	action << "op1 varchar(50),";
	action << "op2 varchar(50),";
	action << "operation varchar(50),";
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

	debug && printf("end_tables\n"); fflush(stdout);
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
	
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){


			vector<string> tokens = tokenize(*it2, " ");
		
			if(tokens.size() == 5){
				string dst = tokens[0];
				string op1 = tokens[2];
				string op2 = tokens[4];
				string operation = tokens[3];
				action << "insert into operations values ('" << dst << "','" << op1 << "','" << op2 << "','" << operation << "'," << id << ");";
			} else {
				string dst = tokens[0];
				string src = tokens[2];
				action << "insert into assigns values ('" << dst << "','" << src << "'," << id << ");";
			}



		}
		
	}


	if( solvable_problem() ){
		get_values();


		for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
			string name = it->first;
			string value = realvalue(name);
			string hint = variables[name].name_hint;
			bool is_memory = (name.substr(0,4) == "mem_");
			action << "insert into results values ('" << name << "','" << value << "','" << hint << "'," << is_memory << "," << id << ");";
			
		}
		
		

		
	}

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}
