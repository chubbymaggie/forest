/*
 * =====================================================================================
 * /
 * |     Filename:  solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/12/2013 02:38:08 PM
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


#include "solver.h"

#define SIZE_STR 512
#define debug false

extern map<string, Variable> variables;
extern set<string> variable_names;
extern vector<string> conditions;

void dump_variables(FILE* file = stdout){

	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(declare-fun %s () %s)\n", tokens[0].c_str(), type.c_str());
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}
	

}

void dump_conditions(FILE* file = stdout){

	for( vector<string>::iterator it = conditions.begin(); it != conditions.end(); it++ ){


		vector<string> tokens = tokenize(*it, " ");



		fprintf(file,"(assert (%s %s %s))\n", tokens[1].c_str(), tokens[0].c_str(), tokens[2].c_str() );
		//debug && printf("\e[33m %s \e[0m\n", it->c_str() );



	}
	
	fprintf(file,"(check-sat)\n");


}

void dump_header(FILE* file = stdout){
	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-logic QF_NIA)\n");

}

void dump_tail(FILE* file = stdout){
	fprintf(file,"(exit)\n");
}

void dump_get(FILE* file = stdout){


	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(get-value (%s))\n", tokens[0].c_str() );
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}

}

void dump_assigns(FILE* file = stdout){

	debug && printf("dump_assigns\n");

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){


			vector<string> tokens = tokenize(*it2, " ");
		
			if(tokens.size() == 5){
				if( tokens[3] == "<=" ){
					continue;
				}
				fprintf(file,"(assert (= %s (%s %s %s)))\n", tokens[0].c_str(), tokens[3].c_str(), tokens[2].c_str(), tokens[4].c_str() );
			} else {
				fprintf(file,"(assert (= %s %s))\n", tokens[0].c_str(), tokens[2].c_str() );
			}



		}
		
	}
}

void get_values(){

	stringstream filename;
	filename << "/tmp/z3_" << rand() << ".smt2";
	FILE* file = fopen(filename.str().c_str(), "w");
	vector<string> ret_vector;

	dump_header(file);
	dump_variables(file);
	dump_assigns(file);
	dump_conditions(file);
	dump_get(file);
	dump_tail(file);

	fclose(file);

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	
	command << "z3 " << filename.str();

	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);

	bool sat = 0;

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		if( it->find("((") == string::npos ) continue;
		vector<string> tokens = tokenize(*it, "() ");
		variables[ tokens[0] ].real_value = tokens[1];
		debug && printf("%s %s\n", tokens[0].c_str(), tokens[1].c_str() );
	}
	

	//for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		//if( it->substr(0,3) == "sat" ) break;
	//}
	
}

bool solvable_problem(){


	stringstream filename;
	filename << "/tmp/z3_" << rand() << ".smt2";
	FILE* file = fopen(filename.str().c_str(), "w");
	vector<string> ret_vector;

	dump_header(file);
	dump_variables(file);
	dump_assigns(file);
	dump_conditions(file);
	dump_tail(file);

	fclose(file);

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	
	command << "z3 " << filename.str();

	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);

	bool sat = 0;

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		if( it->substr(0,3) == "sat" ) sat = 1;
	}
	
	return sat;
	
	
}

void insert_variable(string name){

	if( name.find("constant") != string::npos )
		return;

	//if(variables[name].contents.size() == 0)
		//return;

	variable_names.insert(name);

}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

string extract_condition(string content){
	int n = (int)content.find("=") + 2;
	return content.substr(n);
}

void push_condition(string condition){

	conditions.push_back( condition );
}

string negation(string condition){

	vector<string> tokens = tokenize(condition, " ");

	if( tokens[1] == "<=" ) return tokens[0] + " > " + tokens[2];

	return condition;
}

string get_last_condition(string name){

	string content = variables[name].contents[variables[name].contents.size()-1];
	string condition = extract_condition(content);

	return condition;

}

string actual(string name){
	stringstream ret; ret << name << "_" << variables[name].contents.size();
	return ret.str();
}

string past(string name){

	stringstream ret;
	if(variables[name].contents.size() == 0)
		ret << name << "_" << "initial";
	else 
		ret << name << "_" << variables[name].contents.size()-1;
	return ret.str();
}

string type(string name){
	if (variables[name].type == "IntegerTyID")
		return "Int";
	else
		return "";
}

string get_type(string name){

	int s1 = name.find("_");
	int s2 = name.find("_", s1+1);
	string name_without_suffix = name.substr(0,s2);

	return type(name_without_suffix);

}

string name( string input ){

	if(input.find("constant") != string::npos ){
		int ini = 9;
		string interm = input.substr(ini);
		int len = interm.find("_");
		string final = interm.substr(0, len);

		return final;
	} else {
		return input;
	}


}

