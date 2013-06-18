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
vector<string> flatened_conditions;
set<string> flatened_variables;

void dump_variables(FILE* file){

	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(declare-fun %s () %s)\n", tokens[0].c_str(), type.c_str());
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}
	

}

void dump_conditions(FILE* file){

	for( vector<string>::iterator it = conditions.begin(); it != conditions.end(); it++ ){


		vector<string> tokens = tokenize(*it, " ");


		if( tokens[1] == "#" ) fprintf(file,"(assert (not (= %s %s)))\n", tokens[0].c_str(), tokens[2].c_str() );
		else                   fprintf(file,"(assert (%s %s %s))\n", tokens[1].c_str(), tokens[0].c_str(), tokens[2].c_str() );
		//debug && printf("\e[33m %s \e[0m\n", it->c_str() );



	}
	
	fprintf(file,"(check-sat)\n");


}

void dump_header(FILE* file){
	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-logic QF_NIA)\n");

}

void dump_tail(FILE* file){
	fprintf(file,"(exit)\n");
}

void dump_get(FILE* file){


	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(get-value (%s))\n", tokens[0].c_str() );
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}

}

bool is_comparison( string operation ){

	if( operation == "<=" ) return true;
	if( operation == ">=" ) return true;
	if( operation == "<"  ) return true;
	if( operation == ">"  ) return true;
	if( operation == "="  ) return true;
	return false;
}

void dump_assigns(FILE* file){

	debug && printf("dump_assigns\n");

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){


			vector<string> tokens = tokenize(*it2, " ");
		
			if(tokens.size() == 5){
				if( is_comparison(tokens[3]) ) continue;

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
		variables[ name_without_suffix(tokens[0]) ].real_value = tokens[1];
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
	if( tokens[1] == ">=" ) return tokens[0] + " < " + tokens[2];
	if( tokens[1] == "="  ) return tokens[0] + " # " + tokens[2];

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

	if (variables[name].type == "IntegerTyID32")
		return "Int";

	if (variables[name].type == "IntegerTyID8")
		return "Int";

	//printf("Unknown type, defaulting to Int\n");
	return "Int";
}

string name_without_suffix( string name ){

	int s1 = name.find("_");
	int s2 = name.find("_", s1+1);
	return name.substr(0,s2);
}

string get_type(string name){

	return type(name_without_suffix(name));

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

bool is_number(const std::string& s) {
    std::string::const_iterator it = s.begin();
    while (it != s.end() && std::isdigit(*it)) ++it;
    return !s.empty() && it == s.end();
}

string first_var(string expr){

	vector<string> tokens = tokenize(expr, "<>()+-*= ");

	vector<string>::iterator it;

	for( it = tokens.begin(); it != tokens.end(); it++ ){
		if( it->find("assert") != string::npos ) continue;
		if( it->find("initial") != string::npos ) continue;
		if( is_number(*it) ) continue;
		break;
	}

	if( it == tokens.end() ) return "";
	else return *it;

	
}

void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

string find_constraint( string name ){
	
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){


			vector<string> tokens = tokenize(*it2, " ");

			if( tokens[0] == name ) return *it2;
		

		}
		
	}
}

string substitute( string var, string expr ){

	string ret = expr;
	string constr_target = find_constraint(var);

	debug && printf("\e[31m assign_target: \e[0m %s\n", constr_target.c_str() );

	vector<string> tokens = tokenize( constr_target, "= ");
	string target;

	if( tokens.size() == 2 )
		target = tokens[1];
	else
		target = "(" + tokens[2] + " " + tokens[1] + " " + tokens[3] + ")";



	myReplace(ret, var, target );

	return ret;

}

void flat_constraint(string constraint){
	
	vector<string> tokens = tokenize(constraint, " ");
	string expr = "(assert (" + tokens[1] + " " + tokens[0] + " " + tokens[2] + "))";

	debug && printf("\e[31m assertion: \e[0m %s\n", expr.c_str());


	while(true) {
		string var = first_var(expr);
		if(var == "") break;
		debug && printf("\e[31m var: \e[0m %s\n", var.c_str());
		string subs = substitute(var, expr);
		debug && printf("\e[31m subs: \e[0m %s\n", subs.c_str());
		expr = subs;
	}

	flatened_conditions.push_back(expr);


}

void flat_variables(){

	for( vector<string>::iterator it = flatened_conditions.begin(); it != flatened_conditions.end(); it++ ){
		vector<string> tokens = tokenize(*it, " +-*=()<>");

		for( vector<string>::iterator it2 = tokens.begin(); it2 != tokens.end(); it2++ ){
			if( is_number(*it2) ) continue;
			if( *it2 == "assert" ) continue;
			flatened_variables.insert( *it2 );
		}
		
	}

	for( set<string>::iterator it = flatened_variables.begin(); it != flatened_variables.end(); it++ ){
		debug && printf("\e[31m flattened_variable \e[0m %s \n", it->c_str() );
	}
	
	

}

void dump_get_flat(FILE* file = stdout ){

	for( set<string>::iterator it = flatened_variables.begin(); it !=flatened_variables.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(get-value (%s))\n", tokens[0].c_str() );
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}

}

void dump_flatened_variables(FILE* file ){

	for( set<string>::iterator it = flatened_variables.begin(); it != flatened_variables.end(); it++ ){

		vector<string> tokens = tokenize(*it, " ");

		string name = tokens[0];
		string type = get_type(*it);

		fprintf(file,"(declare-fun %s () %s)\n", tokens[0].c_str(), type.c_str());
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}
	

}

void dump_flatened_conditions(FILE* file ){

	for( vector<string>::iterator it = flatened_conditions.begin(); it != flatened_conditions.end(); it++ ){

		fprintf(file,"%s\n", it->c_str() );
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}

	fprintf(file, "(check-sat)\n");

}

bool allavailable(string expr, set<string> available){

	//printf("\e[31m allavailable \e[0m %s\n", expr.c_str() );

	vector<string> tokens = tokenize(expr, "+= ");

	for ( unsigned int i = 1; i < tokens.size(); i++) {
		if( available.find(tokens[i]) == available.end() ) return false;
	}

	return true;
	
}

string next_with_all_available( set<string> available, set<string> processed ){



	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){

			//printf("\e[31m next_with_all_available \e[0m %s\n", it2->c_str() ); fflush(stdout);
			bool all_available = allavailable(*it2, available);

			if( all_available ){
				if( processed.find(*it2) == processed.end() ){
					//printf("encontrado\n");
					return *it2;
				} else {
					//printf("ya hecho\n");
				}
			}

		}
	}

	return "";
	

}

void real_execution( string expr ){
	

	vector<string> tokens = tokenize(expr, " ");

	//for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
		//printf("%s ", it->c_str() );
	//} printf("\n");
	
	if( tokens.size() == 3 ){

		if( tokens[1] == "=" ) variables[ tokens[0] ].real_value = variables[ tokens[2] ].real_value;

		debug && printf("\e[31m expr \e[0m %s\n", expr.c_str());
		debug && printf("\e[31m tokens[2].real_value \e[0m %s\n", variables[ tokens[2] ].real_value.c_str() );
		debug && printf("\e[31m tokens[0].real_value \e[0m %s\n", variables[ tokens[0] ].real_value.c_str() );

	}

	if( tokens.size() == 5 ){

		if( tokens[3] == "+" ){
			stringstream result; result << stoi(realvalue( tokens[2] )) + stoi(realvalue( tokens[4] ));
			variables[tokens[0]].real_value = result.str();
		}

		debug && printf("\e[31m expr \e[0m %s\n", expr.c_str());
		debug && printf("\e[31m tokens[2].real_value \e[0m %s\n", variables[ tokens[2] ].real_value.c_str() );
		debug && printf("\e[31m tokens[4].real_value \e[0m %s\n", variables[ tokens[4] ].real_value.c_str() );
		debug && printf("\e[31m tokens[0].real_value \e[0m %s\n", variables[ tokens[0] ].real_value.c_str() );

	}



}

void print_available(set<string> in){

	for( set<string>::iterator it = in.begin(); it != in.end(); it++ ){
		debug && printf("%s\n", it->c_str() );
	}
	
}

void get_values_flat(){

	stringstream filename;
	filename << "/tmp/z3_" << rand() << ".smt2";
	FILE* file = fopen(filename.str().c_str(), "w");
	vector<string> ret_vector;

	dump_header(file);
	dump_flatened_variables(file);
	dump_flatened_conditions(file);
	dump_get_flat(file);
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


	set<string> available_vars;

	debug && printf("\e[31m get_values_flat \e[0m %s %d\n", filename.str().c_str(), ret_vector.size() );

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		//printf("it %s\n", it->c_str());
		if( it->find("((") == string::npos ) continue;
		vector<string> tokens = tokenize(*it, "() ");
		variables[ tokens[0] ].real_value = tokens[1];
		available_vars.insert(tokens[0]);
		//printf("\e[31m insert \e[0m %s\n", tokens[0].c_str() );
		debug && printf("%s %s\n", tokens[0].c_str(), tokens[1].c_str() );
	}


	for( set<string>::iterator it = available_vars.begin(); it != available_vars.end(); it++ ){
		debug && printf("available_var %s\n", it->c_str());
	}

	
	set<string> processed;



	while( true ){

		//dump_assigns();
		//print_available(available_vars);

		string expr_with_all_available = next_with_all_available(available_vars, processed);
		if( expr_with_all_available == "" ) break;
		debug && printf("\e[31m next_with_all_available \e[0m %s\n", expr_with_all_available.c_str());
		processed.insert( expr_with_all_available );

		
		vector<string> tokens = tokenize(expr_with_all_available, " ");
		available_vars.insert(tokens[0]);

		real_execution(expr_with_all_available);
	}
	
}

void flat_problem(){

	for( vector<string>::iterator it = conditions.begin(); it != conditions.end(); it++ ){

		flat_constraint(*it);
		
	}

	flat_variables();

	get_values_flat();
	//dump_flatened_variables();
	


}

