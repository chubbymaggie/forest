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

#include "operators.h"
#include "solver.h"

#define debug false
#define SIZE_STR 512

int alloca_pointer = 0;
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
	if( variables[op1].type == "" )
		variables[op1].type = variables[dst].type;


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

	debug && printf("\e[31m binary_operation %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _op1, _op2, _operation, 
			                                                        op1.c_str(), realvalue(op1).c_str(),
									        op2.c_str(), realvalue(op2).c_str(),
										_dst, realvalue(dst).c_str() );
}

void load_instr(char* _dst, char* _addr){
	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem_" + realvalue(addr);

	assign_instruction(src, dst);

	debug && printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _addr,
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

	debug && printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",_src, _addr,
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

	debug && printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _cmp1, _cmp2, _type, 
			                                                 cmp1.c_str(), realvalue(cmp1).c_str(),
									 cmp2.c_str(), realvalue(cmp2).c_str(),
									 dst.c_str(), realvalue(dst).c_str() );
}

bool br_instr_cond(char* _cmp){

	string cmp = string(_cmp);

	debug && printf("\e[31m conditional_branch_instr %s\e[0m. %s %s\n", _cmp, cmp.c_str(), realvalue(cmp).c_str() );

	for( vector<string>::iterator it = variables[cmp].contents.begin(); it != variables[cmp].contents.end(); it++ ){
		debug && printf("\e[32m content \e[0m %s\n", it->c_str());
	}

	string condition = get_last_condition(cmp);

	if(realvalue(cmp) == "true"){
		push_condition(negation(condition));

	} else {
		push_condition(condition);

	}

	if( fork() ){
		return variables[cmp].real_value == "true";
	} else {
		if( solvable_problem() ){
			get_values();
			return variables[cmp].real_value != "true";
		} else {
			exit(0);
		}
	}

}

void br_instr_incond(){

	debug && printf("\e[31m inconditional_branch_instr\e[0m\n" );

}

void begin_bb(char* name){
	debug && printf("\e[31m begin_bb %s \e[0m\n", name );
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

	debug && printf("\e[31m alloca_instr %s %s\e[0m. %s %s %s %s\n",reg.c_str(), type.c_str(), reg.c_str(), realvalue(reg).c_str(), mem_var.str().c_str(), realvalue(mem_var.str()).c_str() );
}

void end_bb(char* name){
	debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

void begin_sim(){
	debug && printf("\e[31m Begin Simulation\e[0m\n" );
}

void end_sim(){
	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	//dump_header();
	//dump_variables();
	//dump_assigns();
	//dump_conditions();
	//dump_tail();
	
	printf("solvable_problem %d\n", solvable_problem() );
	get_values();
	
}

