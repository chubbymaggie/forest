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
#define UNDERSCORE "_"

map<string, Variable> variables;
set<NameAndPosition> variable_names;
vector<string> flatened_conditions;
set<string> flatened_variables;
extern string actual_function;
vector<Condition> conditions;
vector<bool> path_stack;


void push_path_stack(bool step){
	path_stack.push_back(step);
}

string content( string name ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	if( variables[name].content == "" ){
		insert_variable(name, actual_function + UNDERSCORE + variables[name].name_hint );
		return name;

	} else {
		return variables[name].content;
	}
}

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
			number_of_underscore != 1 && // main_registerunderscoreval mem_9
			number_of_underscore != 0    // 0
	)
		return false;

	if( number_of_underscore == 1 ){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if(tokens[1].substr(0,8) != "register" &&
		   tokens[0].substr(0,3) != "mem" 
		  ) return false;
	}

	if( number_of_underscore  == 0 ){
		if( !is_number(name) )
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
	
	string ret;

	if( tokens[tokens.size() - 3] == "-" )
		ret = "-" + tokens[tokens.size() - 2];
	else 
		ret = tokens[tokens.size() - 2];

	//printf("ret %s\n", ret.c_str() );
	assert( is_number(ret) && "Result is not a number");


	return ret;
}

void set_real_value(string varname, string value, string fn_name ){

	if(!check_mangled_name(name(varname))) assert(0 && "Wrong name for set_real_value");

	variables[ name(varname, fn_name) ].real_value = value;
}


void set_real_value_mangled(string varname, string value ){

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[varname].real_value = value;
}

void set_real_value(string varname, string value ){

	if(!check_mangled_name(name(varname))) assert(0 && "Wrong name for set_real_value");

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

void set_name_hint(string name, string hint){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for set_name_hint");
	variables[name].name_hint = hint;

}


string name_without_suffix( string name ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for name_without_suffix");

	int s1 = name.find(UNDERSCORE);
	int s2 = name.find(UNDERSCORE, s1+1);
	return name.substr(0,s2);
}


string get_sized_type(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for sized type");

	if (variables[name].type == "IntegerTyID32")
		return "Int32";

	if (variables[name].type == "IntegerTyID8")
		return "Int8";

	if (variables[name].type == "IntegerTyID16")
		return "Int16";

	if (variables[name].type == "FloatTyID")
		return "Float32";

	if (variables[name].type == "DoubleTyID")
		return "Float64";

	printf("name %s type %s\n", name.c_str(), variables[name].type.c_str() );

	assert(0 && "Unknown Type");

	return "Int";

}


string get_type(string name){

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

	if (variables[name].type == "Real")
		return "Real";

	if (variables[name].type == "bool")
		return "bool";

	if (variables[name].type == "Pointer")
		return "Pointer";


	printf("name %s type %s\n", name.c_str(), variables[name].type.c_str() );

	assert(0 && "Unknown Type");

	return "Int";

}

bool is_number(const std::string& s) {

	if( s== "true" || s== "false") return true;

	if(s.substr(0,1) == "-") return is_number(s.substr(1));

	//printf("%s\n", s.substr(0,s.find(".")).c_str() );
	//printf("%s\n", s.substr(s.find(".")+1).c_str() );
	if( s.find(".") != string::npos ) return 
		is_number(s.substr(0,s.find("."))) &&
		is_number(s.substr(s.find(".")+1));

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

	if(input.substr(0,9) != "constant_" && input.substr(0,4) != "mem_")
		myReplace(input, UNDERSCORE, "underscore" );

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

string realvalue_mangled(string varname){

	//printf("\e[33m realvalue_mangled \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for realvalue_mangled");


	if( varname.find("constant") != string::npos )
		return varname.substr(9);
	else if( variables[varname].real_value == "" )
		return "0";
	else
		return variables[varname].real_value;
}

string realvalue(string varname){

	//printf("\e[33m realvalue \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(name(varname))) assert(0 && "Wrong name for realvalue");



	if( varname.find("constant") != string::npos )
		return varname.substr(9);
	else if( variables[name(varname)].real_value == "" )
		return "0";
	else
		return variables[name(varname)].real_value;

}


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

bool get_is_propagated_constant(string varname){
	if(!check_mangled_name(name( varname))) assert(0 && "Wrong src for assign");
	return variables[name(varname)].is_propagated_constant;
}

void set_is_propagated_constant(string varname){
	if(!check_mangled_name(name(varname))) assert(0 && "Wrong src for assign");

	variables[name(varname)].is_propagated_constant = true;

}

bool is_constant(string varname){
	if(!check_mangled_name(name(varname))) assert(0 && "Wrong src for assign");

	return varname.substr(0,9) == "constant" UNDERSCORE;

}

void assign_instruction(string src, string dst, string fn_name){

	if(!check_mangled_name(name(src))) assert(0 && "Wrong src for assign");
	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for assign");


	debug && printf("\n\e[32m Assign_instruction %s = %s \e[0m\n", name(dst, fn_name).c_str(), name(src).c_str() );

	variables[ name(dst, fn_name) ].content = content( name(src) );

	set_real_value( dst, realvalue(src), fn_name );

	settype(name(dst, fn_name), get_type(name(src)));

	if( get_is_propagated_constant(src) )
		set_is_propagated_constant(dst);

	if( is_constant(src) )
		set_is_propagated_constant(dst);


	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s\n", variables[ name(dst, fn_name) ].content.c_str(), variables[name(dst, fn_name)].type.c_str() );

}


void binary_instruction(string dst, string op1, string op2, string operation){

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for binary_instruction");
	if(!check_mangled_name(name(op1))) assert(0 && "Wrong op1 for binary_instruction");
	if(!check_mangled_name(name(op2))) assert(0 && "Wrong op2 for binary_instruction");

	debug && printf("\n\e[32m Binary_instruction %s = %s %s %s\e[0m\n", name(dst).c_str(), name(op1).c_str(), operation.c_str(), name(op2).c_str() );


	stringstream content_ss;


	if( operation == "#" )
		content_ss << "(not (= " << content( name(op1) ) << " " <<  content( name(op2) ) << "))";
	else if (operation == "%")
		content_ss << "(mod " << content( name(op1) ) << " " <<  content( name(op2) ) << ")";
	else 
		content_ss << "(" << operation << " " << content( name(op1) ) << " " <<  content( name(op2) ) << ")";

	//debug && printf("\e[31m type \e[0m %s \e[31m op2 \e[0m %s \e[31m operation \e[0m %s\n", variables[name(op1)].type.c_str(), op2.c_str(), operation.c_str() );
	if( variables[name(op1)].type == "bool" && op2 == "constant" UNDERSCORE "0" && operation == "#" ){
		content_ss.str("");
		content_ss << content(name(op1));
	}


	variables[name(dst)].content = content_ss.str();

	if( variables[name(op1)].type != "" )
		settype(name(dst), get_type(name(op1)));
	else
		settype(name(dst), get_type(name(op2)));




	if( get_is_propagated_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( get_is_propagated_constant(op1) && is_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( is_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}




	if(operation == "<="){
		set_real_value(dst, ( stoi(realvalue(op1) ) <= stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == ">="){
		set_real_value(dst, ( stoi(realvalue(op1) ) >= stoi( realvalue(op2) ) )?"true":"false" );
	}


	if(operation == "<"){
		set_real_value(dst, ( stoi(realvalue(op1) ) < stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == ">"){
		set_real_value(dst, ( stoi(realvalue(op1) ) > stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == "="){
		set_real_value(dst, ( stoi(realvalue(op1) ) == stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == "#"){
		set_real_value(dst, ( stoi(realvalue(op1) ) != stoi( realvalue(op2) ) )?"true":"false" );
	}


	if(operation == "+"){
		stringstream result; result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		set_real_value(dst, result.str());
	}

	if(operation == "-"){
		stringstream result; result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		set_real_value(dst, result.str());
	}

	if(operation == "*"){
		stringstream result; result << stoi(realvalue(op1)) * stoi(realvalue(op2));
		set_real_value(dst, result.str());
	}


	if(operation == "/"){
		stringstream result; result << stoi(realvalue(op1)) / stoi(realvalue(op2));
		set_real_value(dst, result.str());
	}


	if(operation == "%"){
		stringstream result; result << stoi(realvalue(op1)) % stoi(realvalue(op2));
		set_real_value(dst, result.str());
	}

	if( variables[name(op1)].type != "" ) variables[name(dst)].type = variables[name(op1)].type;
	if( variables[name(op2)].type != "" ) variables[name(dst)].type = variables[name(op2)].type;


	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s\n",
                 variables[ name(dst) ].content.c_str(), variables[name(dst)].type.c_str(), realvalue(dst).c_str() );


}


int show_problem(){

	dump_header();
	dump_variables();
	dump_conditions();
	dump_get();
	dump_tail();

	stringstream filename; filename << "/tmp/z3-" << rand() << ".smt2";

	debug && printf("\e[31m filename \e[0m %s\n", filename.str().c_str() );

	FILE* file = fopen(filename.str().c_str(), "w");

	dump_header(file);
	dump_variables(file);
	dump_conditions(file);
	dump_get(file);
	dump_tail(file);

	fclose(file);



	fflush(stdout);

	getchar();
}


void print_path_stack(){


	debug && printf("\e[33m Path_stack \e[0m");
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		debug && printf("%s", (*it)?"T":"F" );
	}
	debug && printf("\n");
	

}


