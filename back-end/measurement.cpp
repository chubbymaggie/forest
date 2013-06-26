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

set<string> visited_bbs;
set<string> visited_fns;
set<string> available_fns;
set<string> available_bbs;

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

	visited_bbs.insert(actual_fn_name + "_" + name);

	debug && printf("\e[31m begin_bb %s \e[0m\n", _name );
}

void end_bb(char* name){
	debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

void begin_sim(char* functions, char* bbs){

	{
		vector<string> tokens = tokenize(functions, ",");
	
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			available_fns.insert(*it);
		}
	}
	

	{
		vector<string> tokens = tokenize(bbs, ",");
	
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			available_bbs.insert(*it);
		}
	}

	debug && printf("\e[31m Begin Simulation\e[0m %s %s\n", functions, bbs );
}

void BeginFn(char* _fn_name){

	string function_name = string(_fn_name);

	actual_fn_name = function_name;

	visited_fns.insert(function_name);

	debug && printf("\e[31m begin_fn %s \e[0m\n", _fn_name);


}

void end_sim(){

	printf("visited fns %lu/%lu\n", visited_fns.size(), available_fns.size() );
	printf("visited bbs %lu/%lu\n", visited_bbs.size(), available_bbs.size() );

	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	
}

