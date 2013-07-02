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

#define SIZE_STR 32768
#define debug true
#define UNDERSCORE "@"

extern map<string, Variable> variables;
extern set<NameAndPosition> variable_names;
vector<string> flatened_conditions;
set<string> flatened_variables;
extern string actual_function;
vector<Condition> conditions;


int count(string name, string character){

    int n = 0;
    string::size_type sz = 0;

    while ( (sz = name.find (character,sz) ) != string::npos  ){
        sz++; /*otherwise you start searching at your previous match*/
        n++;
    }
    return n;

}

//bool check_name(string name){

	//int number_of_underscore = count(name, UNDERSCORE);
	//if(
			//number_of_underscore != 0 &&
			//number_of_underscore != 3 &&
			//number_of_underscore != 2 &&
			//number_of_underscore != 1 &&
			//number_of_underscore != 4
	//)
		//return false;

	//if(number_of_underscore == 4){
		//vector<string> tokens = tokenize(name, UNDERSCORE);
		//if(tokens[3] != "offset")
			//return false;
	//}

	//if(number_of_underscore == 3){
		//vector<string> tokens = tokenize(name, UNDERSCORE);
		//if(tokens[2] != "offset")
			//return false;
	//}

	//if( name.substr(0,4) == "mem" UNDERSCORE )
		//if(!is_number(name.substr(4))) return false;

	//if( name.substr(0,9) == "constant" UNDERSCORE )
		//if(!is_number(name.substr(9))) return false;

	//if( name.find(UNDERSCORE) == string::npos ){
		//if(!is_number(name)) return false;
	//}

	//return true;

//}

bool check_mangled_name(string name){

	//printf("check mangled name %s\n", name.c_str());
	int number_of_underscore = count(name, UNDERSCORE);
	if(
			number_of_underscore != 2 && // main_register_r1
			number_of_underscore != 0 && // 2
			number_of_underscore != 1 && // mem_9
			number_of_underscore != 4 // main_register_r1_offset_0
	)
		return false;

	if( number_of_underscore == 1 ){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if(tokens[0] != "mem") return false;
	}

	if( number_of_underscore == 4 ){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if(tokens[3] != "offset") return false;
	}

	if( number_of_underscore == 0 ){
		if( !is_number(name) ) return false;
	}

	return true;

}

bool check_unmangled_name(string name){
	//printf("check unmangled name %s\n", name.c_str());
	int number_of_underscore = count(name, UNDERSCORE);
	if(
			number_of_underscore != 1 && // register_retval
			number_of_underscore != 2 && // register_x_addr
			number_of_underscore != 3 // register_r1_offset_0
	)
		return false;

	if(number_of_underscore == 2){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if(tokens[2] != "addr")
			return false;
	}

	if(number_of_underscore == 3){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if(tokens[2] != "offset")
			return false;
	}

	return true;

}

void dump_variables(FILE* file){

	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = get_type(it->name);

		fprintf(file,"(declare-fun %s () %s)\n", tokens[0].c_str(), type.c_str());
		//debug && printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
		
	}
	

}

void dump_conditions(FILE* file){

	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		fprintf(file,"(assert %s)\n", it->cond.c_str() );
	}
	
	fprintf(file,"(check-sat)\n");


}

void dump_header(FILE* file){
	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");

}

void dump_tail(FILE* file){
	fprintf(file,"(exit)\n");
}

void dump_get(FILE* file){


	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n", it->name.c_str(), it->name.c_str() );
	}
	
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if( it->second.content == "" ) continue;
		fprintf(file,"(get-value (%s)); %s\n", it->second.content.c_str(), it->first.c_str() );
	}
	
}

string result_get(string get_str){

	vector<string> tokens = tokenize( get_str, "() ");

	//for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
		//printf("%s\n", it->c_str() );
	//}
	


	if( tokens[tokens.size() - 3] == "-" )
		return "-" + tokens[tokens.size() - 2];
	else 
		return tokens[tokens.size() - 2];

}

void set_real_value(string varname, string value, string fn_name ){

	if(!check_unmangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[ name(varname, fn_name) ].real_value = value;
}


void set_real_value_mangled(string varname, string value ){

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[varname].real_value = value;
}

void set_real_value(string varname, string value ){

	if(!check_unmangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[ name(varname) ].real_value = value;
}

void get_values(){

	stringstream filename;
	filename << "/tmp/z3_" << getpid() << ".smt2";

	debug && printf("\e[31m filename get_values \e[0m %s\n", filename.str().c_str() );

	FILE* file = fopen(filename.str().c_str(), "w");
	vector<string> ret_vector;

	dump_header(file);
	dump_variables(file);
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


	vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++,it_ret++ ){

		string varname = it->name;
		string value = result_get(*it_ret);

		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);
		//variables[varname].real_value = value;

	}


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if( it->second.content == "" ) continue;

		string name = it->first;
		string value = result_get(*it_ret);


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);
		//variables[name].real_value = value;

		it_ret++;
	}









	//map<string,Variable>::iterator it_var = variables.begin();
	//vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	//for( map<string,Variable>::iterator it = it_var; it != variables.end(); it++ ){

		//if( it->second.content == "" ) continue;
	
		//string name = it->first;
		//string value = result_get(*it_ret);

		//printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		//it_ret++;

	//}

}

bool solvable_problem(){

	stringstream filename;
	filename << "/tmp/z3_" << getpid() << ".smt2";

	debug && printf("\e[31m filename solvable_problem \e[0m %s\n", filename.str().c_str() );

	FILE* file = fopen(filename.str().c_str(), "w");
	vector<string> ret_vector;

	dump_header(file);
	dump_variables(file);
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

void insert_variable(string name, string position){


	if(!check_mangled_name(name)) assert(0 && "Wrong name for insert_variable");


	if( name.find("constant") != string::npos )
		return;

	if( is_number(name) )
		return;

	//if(variables[name].contents.size() == 0)
		//return;
		
	debug && printf("\e[32m Insert_variable \e[0m name %s hint %s position %s\n", name.c_str(), variables[name].name_hint.c_str(), position.c_str() );

	NameAndPosition nandp = {name, position};
	variable_names.insert(nandp);

}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

void push_condition(string cond, string fn, vector<string> joints ){

	set<string> joints_set = set<string>(joints.begin(), joints.end());

	Condition condition = { cond, fn, joints_set };
	conditions.push_back( condition );
}

string negation(string condition){

	stringstream negation_ss;
	negation_ss << "(not " << string(condition) << ")";

	return negation_ss.str();
}

void settype(string name, string type){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for settype");
	variables[name].type = type;

}

string type(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for type");

	if(name.substr(0,9) == "constant" UNDERSCORE) return "IntegerTyID32";
	if( is_number(name) ) return "IntegerTyID32";

	if (variables[name].type == "IntegerTyID32")
		return "Int";

	if (variables[name].type == "DoubleTyID")
		return "Real";

	if (variables[name].type == "IntegerTyID64")
		return "Int";

	if (variables[name].type == "IntegerTyID8")
		return "Int";

	if (variables[name].type == "IntegerTyID16")
		return "Int";

	if (variables[name].type == "PointerTyID")
		return "Int";

	if (variables[name].type == "Int")
		return "Int";

	if (variables[name].type == "FloatTyID")
		return "Real";

	if (variables[name].type == "bool")
		return "bool";

	printf("name %s type %s\n", name.c_str(), variables[name].type.c_str() );

	assert(0 && "Unknown Type");

	return "Int";
}

string name_without_suffix( string name ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for name_without_suffix");

	int s1 = name.find(UNDERSCORE);
	int s2 = name.find(UNDERSCORE, s1+1);
	return name.substr(0,s2);
}

string get_type(string name){

	//return type(name_without_suffix(name));
	return type(name);

}

bool is_number(const std::string& s) {
    std::string::const_iterator it = s.begin();
    while (it != s.end() && std::isdigit(*it)) ++it;
    return !s.empty() && it == s.end();
}

void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

string name( string input, string fn_name ){

	if(input.find("constant") != string::npos ){
		int ini = 9;
		string interm = input.substr(ini);
		int len = interm.find(UNDERSCORE);
		string final = interm.substr(0, len);

		return final;
	} else if (input.substr(0,4) == "mem" UNDERSCORE ){
		return input;
	} else {
		return ((fn_name == "")?actual_function:fn_name) + UNDERSCORE + input;
		//return input;
	}


}

void clean_conditions_stack(string name){
	
	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if( it->joints.find(name) != it->joints.end() ){
			conditions.erase(it);
			it--;
		}
	}
	

}

