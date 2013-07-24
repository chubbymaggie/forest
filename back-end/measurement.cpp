/*
 * =====================================================================================
 * /
 * |     Filename:  measurement.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 09:22:48 AM
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


#include "measurement.h"

using namespace std;

#define debug true

#define UNDERSCORE "_"

set<string> visited_bbs;
set<string> visited_fns;
set<string> available_fns;
set<string> available_bbs;
map<string, vector<string> > test_vectors;
vector<string> fn_stack;
vector<bool> path_stack;

string actual_fn_name;

vector<string> tokenize(const string& str,const string& delimiters) {
	vector<string> tokens;
    	
	// skip delimiters at beginning.
    	string::size_type lastPos = str.find_first_not_of(delimiters, 0);
    	
	// find first "non-delimiter".
    	string::size_type pos = str.find_first_of(delimiters, lastPos);

    	while (string::npos != pos || string::npos != lastPos)
    	{
		// found a token, add it to the vector.
		tokens.push_back(str.substr(lastPos, pos - lastPos));
	
		// skip delimiters.  Note the "not_of"
		lastPos = str.find_first_not_of(delimiters, pos);
	
		// find next "non-delimiter"
		pos = str.find_first_of(delimiters, lastPos);
    	}

	return tokens;
}

void begin_bb(char* _name){

	string name = string(_name);

	visited_bbs.insert(actual_fn_name + UNDERSCORE + name);

	debug && printf("\e[31m begin_bb %s \e[0m\n", _name );
}

void end_bb(char* name){
	//debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

map<string, vector<string> > load_test_vectors(){

	debug && printf("load_test_vectors\n");

	vector<string> free_variables;
	map<string, vector<string> > ret;

	FILE* file;
	char line[128];

	debug && printf("loading free_variables\n"); fflush(stdout);

	file = fopen ( "free_variables", "r" );
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		vector<string> tokens = tokenize(string(line), " ");
		string name = tokens[0];

		free_variables.push_back(name);
	}
	fclose ( file );


	debug && printf("loading test_vectors\n"); fflush(stdout);

	file = fopen ( "vectors", "r" );
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;

		vector<string> tokens = tokenize(string(line), " ");

		for ( unsigned int i = 0; i < tokens.size(); i++) {
			debug && printf("load_vector %s %s\n", free_variables[i].c_str(), tokens[i].c_str() );
			ret[ free_variables[i] ].push_back(tokens[i]);
		}
		


	}
	fclose ( file );

	debug && printf("End_loading\n"); fflush(stdout);

	return ret;
	
}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

short stos(string str){
	short ret;
	int ret_i;
	sscanf(str.c_str(), "%d", &ret_i);
	ret = ret_i;
	return ret;
}


short stoc(string str){
	char ret;
	int ret_i;
	sscanf(str.c_str(), "%d", &ret_i);
	ret = ret_i;
	return ret;
}

int vector_int(char* _name){
	
	string name = string(_name);


	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_int %s %s\n", _name, ret.c_str());

	return stoi(ret);
}


short vector_short(char* _name){

	string name = string(_name);


	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_short %s %s\n", _name, ret.c_str());

	short ret_s = stos(ret);

	return ret_s;
}


char vector_char(char* _name){

	string name = string(_name);

	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_char %s %s\n", _name, ret.c_str());

	char ret_c = stoc(ret);

	return ret_c;
}


void begin_sim(char* functions, char* bbs){

	start_database();
	test_vectors = load_test_vectors();

	{
		debug && printf("Inserting functions %s\n", functions);
		vector<string> tokens = tokenize(functions, ",");
	
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			//if( *it == "test"       ) continue;
			//if( *it == "begin_bb"   ) continue;
			//if( *it == "end_bb"     ) continue;
			//if( *it == "BeginFn"    ) continue;
			//if( *it == "vector_int" ) continue;
			debug && printf("Insert_fn %s\n", it->c_str());
			available_fns.insert(*it);
		}
	}
	

	{
		debug && printf("Inserting bbs %s\n", bbs);
		vector<string> tokens = tokenize(bbs, ",");
	
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			//if( *it == "main_entry" ) continue;
			//if( *it == "main_bb" ) continue;
			//if( *it == "main_bb2" ) continue;
			debug && printf("Insert_bb %s\n", it->c_str());
			available_bbs.insert(*it);
		}
	}

	debug && printf("\e[31m Begin Simulation\e[0m %s %s\n", functions, bbs );
}

void BeginFn(char* _fn_name){

	string function_name = string(_fn_name);

	actual_fn_name = function_name;

	fn_stack.push_back(function_name);

	visited_fns.insert(function_name);

	debug && printf("\e[31m begin_fn %s \e[0m\n", _fn_name);


}


void EndFn(){

	assert(fn_stack.size() && "Empty stack");

	debug && printf("\e[31m end_fn %lu \e[0m\n", fn_stack.size());

	printf("size %lu\n", fn_stack.size());
	fn_stack.erase(fn_stack.end()-1);

	if(fn_stack.size()){
		string function_name = fn_stack[fn_stack.size()-1];
		actual_fn_name = function_name;
	}



}


void br_instr_cond(bool value){

	printf("br_instr_cond %d\n", value);

	path_stack.push_back(value);
	insert_problem();

}



void end_sim(){

	debug && printf("visited fns %lu/%lu\n", visited_fns.size(), available_fns.size() );
	debug && printf("visited bbs %lu/%lu\n", visited_bbs.size(), available_bbs.size() );

	debug && printf("visited_fns\n");
	for( set<string>::iterator it = visited_fns.begin(); it != visited_fns.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");


	debug && printf("available_fns\n");
	for( set<string>::iterator it = available_fns.begin(); it != available_fns.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");


	
	debug && printf("visited_bbs\n");
	for( set<string>::iterator it = visited_bbs.begin(); it != visited_bbs.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");


	debug && printf("available_bbs\n");
	for( set<string>::iterator it = available_bbs.begin(); it != available_bbs.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");



	stringstream value;

	value.str("");
	value << visited_fns.size() << "/" << available_fns.size() << " ( " <<
		(int)(100.0*(float)visited_fns.size()/(float)available_fns.size())
		<< " % )";

	insert_measurement("visited_fns", value.str());

	value.str("");
	value << visited_bbs.size() << "/" << available_bbs.size() << " ( " <<
		(int)(100.0*(float)visited_bbs.size()/(float)available_bbs.size())
		<< " % )";
	insert_measurement("visited_bbs", value.str());

	end_database();

	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	

}

int branches_count = 0;

void br_count(){
	branches_count++;
}

void end_count(){
	printf("Number of branches %d\n", branches_count);
}


