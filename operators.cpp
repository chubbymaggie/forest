/*
 * =====================================================================================
 * /
 * |     Filename:  operators.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/15/2013 05:27:48 PM
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

#include <stdio.h>
#include <string>
#include <map>
#include <sstream>
#include <vector>
#include <set>

extern "C" void binary_op(char*, char*, char*, char*);
extern "C" void load_instr(char*, char*);
extern "C" void store_instr(char*, char*);
extern "C" void cmp_instr(char*, char*, char*, char*);
extern "C" bool br_instr_cond(char*);
extern "C" void br_instr_incond();
extern "C" void begin_bb(char* a);
extern "C" void end_bb(char* a);
extern "C" void alloca_instr(char* a, char* b);
extern "C" void begin_sim();
extern "C" void end_sim();

using namespace std;

int alloca_pointer = 0;

typedef struct Variable {
	string real_value;
	string type;
	vector<string> contents;
} Variable;

map<string, Variable> variables;
set<string> variable_names;
vector<string> conditions;


string realvalue(string name){

	if( name.find("constant") != string::npos )
		return name.substr(9);
	else if( variables[name].real_value == "" )
		return "0";
	else
		return variables[name].real_value;

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



void assign_instruction(string src, string dst){

	stringstream content;

	content << name(actual(dst)) << " = " << name(past(src));
	variables[string(dst)].contents.push_back( content.str() );

	//insert_variable(actual(dst));
	insert_variable(past(src));

	variables[dst].real_value = realvalue(src);

	if( variables[dst].type == "" )
		variables[dst].type = variables[src].type;
	if( variables[src].type == "" )
		variables[src].type = variables[dst].type;

}


void binary_instruction(string dst, string op1, string op2, string operation){

	stringstream content;
	content << name( actual(dst) ) << " = " << name(past(op1)) << " " << operation << " " << name(past(op2));
	variables[dst].contents.push_back( content.str() );

	//insert_variable(actual(dst));
	insert_variable(past(op1));
	insert_variable(past(op2));

	if( variables[dst].type == "" )
		variables[dst].type = variables[op1].type;
	if( variables[src].type == "" )
		variables[src].type = variables[op1].type;


	if(operation == "<="){
		variables[dst].real_value = ( stoi(realvalue(op1) ) <= stoi( realvalue(op2) ) )?"true":"false";
	}

	if(operation == "+"){
		stringstream result; result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		variables[dst].real_value = result.str();
	}

	if(operation == "-"){
		stringstream result; result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		variables[dst].real_value = result.str();
	}


}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){
	string dst = string(_dst);
	string op1 = string(_op1);
	string op2 = string(_op2);
	string operation = string(_operation);

	binary_instruction(dst, op1, op2, operation);

	printf("\e[31m binary_operation %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _op1, _op2, _operation, 
			                                                        op1.c_str(), realvalue(op1).c_str(),
									        op2.c_str(), realvalue(op2).c_str(),
										_dst, realvalue(dst).c_str() );
}

void load_instr(char* _dst, char* _addr){
	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem_" + realvalue(addr);

	assign_instruction(src, dst);

	printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _addr,
								    addr.c_str(), realvalue(addr).c_str(),
								    src.c_str(), realvalue(src).c_str(),
							            dst.c_str(), realvalue(dst).c_str()
								    );
}



void store_instr(char* _src, char* _addr){
	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem_" + realvalue(string(_addr)) ;
	assign_instruction(src, dst);

	printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",_src, _addr,
			                                           src.c_str(), realvalue(src).c_str(),
								   addr.c_str(), realvalue(addr).c_str(),
								   dst.c_str(), realvalue(dst).c_str() );


}



void cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){


	string dst  = string(_dst);
	string cmp1 = string(_cmp1);
	string cmp2 = string(_cmp2);
	string type = string(_type);

	//printf("real_value cmp1 %s\n", realvalue(cmp1).c_str() );
	//printf("real_value cmp2 %s\n", realvalue(cmp2).c_str() );
	

	binary_instruction(dst, cmp1, cmp2, type);

	printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _cmp1, _cmp2, _type, 
			                                                 cmp1.c_str(), realvalue(cmp1).c_str(),
									 cmp2.c_str(), realvalue(cmp2).c_str(),
									 dst.c_str(), realvalue(dst).c_str() );
}

string extract_condition(string content){
	int n = (int)content.find("=") + 2;
	return content.substr(n);
}

void push_condition(string name){


	string content = variables[name].contents[variables[name].contents.size()-1];
	string condition = extract_condition(content);

	conditions.push_back( condition );
}




bool br_instr_cond(char* _cmp){



	string cmp = string(_cmp);

	printf("\e[31m conditional_branch_instr %s\e[0m. %s %s\n", _cmp, cmp.c_str(), realvalue(cmp).c_str() );

	for( vector<string>::iterator it = variables[cmp].contents.begin(); it != variables[cmp].contents.end(); it++ ){
		printf("\e[32m content \e[0m %s\n", it->c_str());
	}

	push_condition(cmp);

	//if( satisfiable(variables, cmp,  ) )

	return variables[cmp].real_value == "true";

}

void br_instr_incond(){

	printf("\e[31m inconditional_branch_instr\e[0m\n" );

}

void begin_bb(char* name){
	printf("\e[31m begin_bb %s \e[0m\n", name );
}

void alloca_instr(char* _reg, char* _type){

	string reg = string(_reg);
	string type = string(_type);

	stringstream rvalue; rvalue << alloca_pointer; 
	variables[reg].real_value = rvalue.str();

	stringstream mem_var; mem_var << "mem_" << rvalue.str().c_str();

	variables[mem_var.str()].real_value = "0";

	variables[mem_var.str()].type = type;

	alloca_pointer++;

	printf("\e[31m alloca_instr %s %s\e[0m. %s %s %s %s\n",reg.c_str(), type.c_str(), reg.c_str(), realvalue(reg).c_str(), mem_var.str().c_str(), realvalue(mem_var.str()).c_str() );
}

void end_bb(char* name){
	printf("\e[31m end_bb %s\e[0m\n", name );
}

void begin_sim(){
	printf("\e[31m Begin Simulation\e[0m\n" );
}

void dump_assigns(){
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		for( vector<string>::iterator it2 = it->second.contents.begin(); it2 != it->second.contents.end(); it2++ ){
			printf("\e[31m %s \e[0m\n", it2->c_str() );
		}
		
	}
}

string type(string name){
	return variables[name].type;
}

string get_type(string name){

	int s1 = name.find("_");
	int s2 = name.find("_", s1+1);
	string name_without_suffix = name.substr(0,s2);

	return type(name_without_suffix);


}

void dump_variables(){

	for( set<string>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
		printf("\e[32m %s %s \e[0m\n", it->c_str(), get_type(*it).c_str() );
	}
	

}

void dump_conditions(){

	for( vector<string>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		printf("\e[33m %s \e[0m\n", it->c_str() );
	}
	


}

void end_sim(){
	printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	dump_variables();
	dump_assigns();
	dump_conditions();
	
}

