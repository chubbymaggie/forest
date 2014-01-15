/*
 * =====================================================================================
 * /
 * |     Filename:  options.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/12/2013 03:43:30 AM
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

#include "options.h"

Options::Options(){}
Options::~Options(){}

void Options::read_options(){


	ifstream input("/tmp/options");
	string line;
	
	while( getline( input, line ) ) {
		
		vector<string> tokens = tokenize(line, " ");

		string key = tokens[0];
		string value = line.substr(key.size()+1);
		options[ tokens[0] ] = value;
		//options[ tokens[0] ] = tokens[1];

		//string value;
		//for ( unsigned int i = 1; i < tokens.size(); i++) {
			//value += tokens[i];
			//value += " ";
		//}

		//options[ tokens[0] ] = value;

		
		
	}
	
	
}

bool Options::cmd_option_bool(string key){
	return options[key] == "true";
}

vector<string> Options::cmd_option_vector_str(string key){

	//printf("cmd_option_vector_str %s\n", options[key].c_str());

	vector<string> tokens = tokenize(options[key], "@");
	return tokens;
}
