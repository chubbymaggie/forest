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
#include <sys/wait.h>

#define debug false
#define see_each_problem false
#define see_flat_problem false
#define SIZE_STR 512

int alloca_pointer = 0;
map<string, Variable> variables;
set<NameAndPosition> variable_names;
vector<pair<string, string> > callstack;
vector<bool> path_stack;

string actual_function;
string actual_bb;

string content( string name ){

	if(!check_name(name)) assert(0 && "Wrong name for content");

	if( variables[name].content == "" ){
		insert_variable(name, actual_function + "_" + variables[name].name_hint );
		return name;

	} else {
		return variables[name].content;
	}
}

string realvalue(string varname){

	if(!check_name(varname)) assert(0 && "Wrong name for realvalue");


	//printf("\e[33m realvalue \e[0m %s\n", varname.c_str() );

	if( varname.find("constant") != string::npos )
		return varname.substr(9);
	else if( variables[name(varname)].real_value == "" )
		return "0";
	else
		return variables[name(varname)].real_value;

}

void set_real_value(string varname, string value, string fn_name ){

	if(!check_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[ name(varname, fn_name) ].real_value = value;
}

void set_real_value(string varname, string value ){

	if(!check_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[ name(varname) ].real_value = value;
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

void assign_instruction(string src, string dst, string fn_name){

	if(!check_name(src)) assert(0 && "Wrong src for assign");
	if(!check_name(dst)) assert(0 && "Wrong dst for assign");


	debug && printf("\n\e[32m Assign_instruction %s = %s \e[0m\n", name(dst, fn_name).c_str(), name(src).c_str() );

	variables[ name(dst, fn_name) ].content = content( name(src) );

	set_real_value( dst, realvalue(src), fn_name );

	variables[ name(dst, fn_name) ].type = variables[name(src)].type;

	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s\n", variables[ name(dst, fn_name) ].content.c_str(), variables[name(dst, fn_name)].type.c_str() );

}

void binary_instruction(string dst, string op1, string op2, string operation){

	if(!check_name(dst)) assert(0 && "Wrong dst for binary_instruction");
	if(!check_name(op1)) assert(0 && "Wrong op1 for binary_instruction");
	if(!check_name(op2)) assert(0 && "Wrong op2 for binary_instruction");

	debug && printf("\n\e[32m Binary_instruction %s = %s %s %s\e[0m\n", name(dst).c_str(), name(op1).c_str(), operation.c_str(), name(op2).c_str() );


	stringstream content_ss;


	if( operation == "#" )
		content_ss << "(not (= " << content( name(op1) ) << " " <<  content( name(op2) ) << "))";
	else if (operation == "%")
		content_ss << "(mod " << content( name(op1) ) << " " <<  content( name(op2) ) << ")";
	else 
		content_ss << "(" << operation << " " << content( name(op1) ) << " " <<  content( name(op2) ) << ")";

	//debug && printf("\e[31m type \e[0m %s \e[31m op2 \e[0m %s \e[31m operation \e[0m %s\n", variables[name(op1)].type.c_str(), op2.c_str(), operation.c_str() );
	if( variables[name(op1)].type == "bool" && op2 == "constant_0" && operation == "#" ){
		content_ss.str("");
		content_ss << content(name(op1));
	}


	variables[name(dst)].content = content_ss.str();

	variables[name(dst)].type = variables[name(op1)].type;







	if(operation == "<="){
		set_real_value(dst, ( stoi(realvalue(op1) ) <= stoi( realvalue(op2) ) )?"true":"false" );
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

void cast_instruction(char* _dst, char* _src, char* _type){

	string dst = string(_dst);
	string src = string(_src);
	string type = string(_type);


	if(!check_name(dst)) assert(0 && "Wrong dst for cast_instruction");
	if(!check_name(src)) assert(0 && "Wrong src for cast_instruction");


	assign_instruction(src,dst);

	debug && printf("\e[31m Cast_instruction %s %s \e[0m. %s %s %s %s\n", name(dst).c_str(), name(src).c_str(),
		                                                              name(src).c_str(), realvalue(src).c_str(),
		                                                              name(dst).c_str(), realvalue(dst).c_str()  );

	if( variables[name(src)].type != "bool" )
		variables[ name(dst) ].type = type;
	else
		variables[ name(dst) ].type = "bool";

}

void CallInstr( char* _fn_name, char* _oplist, char* _fn_oplist, char* _ret_to ){


	string fn_name           = string(_fn_name);
	vector<string> oplist    = tokenize( string(_oplist), ",");
	vector<string> fn_oplist = tokenize( string(_fn_oplist), ",");
	string ret_to            = string(_ret_to);

	if( fn_name.substr(0,1) == "_" ) fn_name = fn_name.substr(1);


	if( oplist.size() && oplist[0] != "register_" ){

	for ( unsigned int i = 0; i < oplist.size(); i++) {

		assign_instruction( oplist[i], fn_oplist[i], fn_name );

	}

	}

	variables[name(ret_to)].name_hint = "return of " + fn_name;

	debug && printf("\e[31m CallInstr %s %s %s %s\e[0m\n", _fn_name, _oplist, _fn_oplist, _ret_to );

	if( ret_to != "register_" )
		callstack.push_back( pair<string, string>(ret_to, actual_function) );


}

void ReturnInstr(char* _retname ){

	string retname = string(_retname);

	if(!check_name(retname)) assert(0 && "Wrong return name for ReturnInstr");


	debug && printf("\e[31m ReturnInstr %s \e[0m size %lu \n", _retname, callstack.size() );

	if( callstack.size() == 0 ) return;

	string last_rg_callstack = callstack[ callstack.size() - 1].first;
	string last_fn_callstack = callstack[ callstack.size() - 1].second;

	callstack.erase( callstack.end() - 1 );

	assign_instruction( retname, last_rg_callstack, last_fn_callstack );


}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){

	string dst = string(_dst);
	string op1 = string(_op1);
	string op2 = string(_op2);
	string operation = string(_operation);


	if(!check_name(dst)) assert(0 && "Wrong dst for binary_op");
	if(!check_name(op1)) assert(0 && "Wrong op1 for binary_op");
	if(!check_name(op2)) assert(0 && "Wrong op2 for binary_op");


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

	if(!check_name(dst)) assert(0 && "Wrong dst for load");
	if(!check_name(addr)) assert(0 && "Wrong addr for load");



	assign_instruction(src, dst);

	debug && printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(addr).c_str(),
								    name(addr).c_str(), realvalue(addr).c_str(),
								    name(src).c_str(), realvalue(src).c_str(),
							            name(dst).c_str(), realvalue(dst).c_str()
								    );

}

void store_instr(char* _src, char* _addr){

	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem_" + realvalue(string(_addr)) ;


	if(!check_name(src)) assert(0 && "Wrong src for store");
	if(!check_name(addr)) assert(0 && "Wrong addr for store");
	if(!check_name(dst)) assert(0 && "Wrong dst for store");


	assign_instruction(src, dst);

	debug && printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",name(src).c_str(), name(addr).c_str(),
			                                           name(src).c_str(), realvalue(src).c_str(),
								   name(addr).c_str(), realvalue(addr).c_str(),
								   name(dst).c_str(), realvalue(dst).c_str() );

}

void cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){

	string dst  = string(_dst);
	string cmp1 = string(_cmp1);
	string cmp2 = string(_cmp2);
	string type = string(_type);

	if(!check_name(dst)) assert(0 && "Wrong dst for compare");
	if(!check_name(cmp1)) assert(0 && "Wrong cmp1 for compare");
	if(!check_name(cmp2)) assert(0 && "Wrong cmp2 for compare");


	binary_instruction(dst, cmp1, cmp2, type);

	debug && printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(cmp1).c_str(), name(cmp2).c_str(), type.c_str(), 
			                                                 name(cmp1).c_str(), realvalue(cmp1).c_str(),
									 name(cmp2).c_str(), realvalue(cmp2).c_str(),
									 name(dst).c_str(), realvalue(dst).c_str() );

	variables[ name(dst) ].type = "bool";
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

void br_instr_incond(){

	debug && printf("\e[31m inconditional_branch_instr\e[0m\n" );

}

void begin_bb(char* name){
	actual_bb = string(name);

	clean_conditions_stack(actual_bb);

	debug && printf("\e[31m begin_bb %s \e[0m\n", name );
}

void end_bb(char* name){
	debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

void alloca_instr(char* _reg, char* _type, char* _size){

	string reg = string(_reg);
	string type = string(_type);

	if(!check_name(reg)) assert(0 && "Wrong dst for alloca");

	stringstream rvalue; rvalue << alloca_pointer; 
	set_real_value(reg,rvalue.str());

	stringstream mem_var; mem_var << "mem_" << rvalue.str().c_str();

	variables[mem_var.str()].real_value = "0";
	variables[mem_var.str()].name_hint = reg;

	int size;
	sscanf(_size, "%d", &size);

	if( type == "ArrayTyID" ){
		for ( unsigned int i = alloca_pointer; i < alloca_pointer + size; i++) {
			stringstream mem_name; mem_name << "mem_" << i;
			stringstream mem_hint; mem_hint << reg << "+" << i;
			variables[ mem_name.str() ].name_hint = mem_hint.str();
		}

		assign_instruction( "constant_0", reg );
	}

	variables[mem_var.str()].type = type;


	alloca_pointer += size;

	debug && printf("\e[31m alloca_instr %s %s %s\e[0m. %s %s %s %s\n", name(reg).c_str(), type.c_str(), _size, name(reg).c_str(), realvalue(reg).c_str(), mem_var.str().c_str(), realvalue(mem_var.str()).c_str() );

}

void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _sizes){

	string dst     = string(_dst);
	string pointer = string(_pointer);
	vector<string> indexes = tokenize(string(_indexes), ",");
	vector<string> sizes   = tokenize(string(_sizes), ",");


	if(!check_name(dst)) assert(0 && "Wrong dst for getelementptr");
	if(!check_name(pointer)) assert(0 && "Wrong dst for getelementptr");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_name(*it)) assert(0 && "Wrong index for getelementptr");
	}
	for( vector<string>::iterator it = sizes.begin(); it != sizes.end(); it++ ){
		if(!check_name(*it)) assert(0 && "Wrong size for getelementptr");
	}
	



	for ( unsigned int i = 0; i < indexes.size(); i++) {
		stringstream namedst; namedst << dst << "_offset_" << i;
		//printf("%s = %s · %s\n", namedst.str().c_str(), indexes[i].c_str(), sizes[i].c_str());
		binary_instruction(namedst.str(), indexes[i], sizes[i], "*");
	}


	for ( unsigned int i = 0; i < indexes.size(); i++) {
		if( i == 0 ){
			stringstream namedst; namedst << dst;
			stringstream nameop1; nameop1 << pointer;
			stringstream nameop2; nameop2 << dst << "_offset_" << i;
			//printf("%s = %s + %s\n", namedst.str().c_str(), nameop1.str().c_str(), nameop2.str().c_str());
			binary_instruction(namedst.str(),nameop1.str(), nameop2.str(), "+");
		} else {
			stringstream namedst; namedst << dst;
			stringstream nameop1; nameop1 << dst;
			stringstream nameop2; nameop2 << dst << "_offset_" << i;
			//printf("%s = %s + %s\n", namedst.str().c_str(), nameop1.str().c_str(), nameop2.str().c_str());
			binary_instruction(namedst.str(), nameop1.str(), nameop2.str(), "+");
		}
	}

	debug && printf("\e[31m getelementptr %s %s %s %s\e[0m. %s %s\n", dst.c_str(), pointer.c_str(), _indexes, _sizes,
		                                                          name(dst).c_str(), realvalue(dst).c_str() );

}

void begin_sim(){
	debug && printf("\e[31m Begin Simulation\e[0m\n" );
	start_database();
	create_tables();
}

void BeginFn(char* _fn_name){

	string fn_name = string(_fn_name);

	if( fn_name.substr(0,1) == "_" )
		actual_function = fn_name.substr(1);
	else
		actual_function = fn_name;


	debug && printf("\e[31m begin_fn %s \e[0m\n", _fn_name);


}

void end_sim(){

	end_database();
	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	//dump_header();
	//dump_variables();
	//dump_assigns();
	//dump_conditions();
	//dump_tail();
	
	//printf("solvable_problem %d\n", solvable_problem() );
	//get_values();
	
}

void print_path_stack(){


	debug && printf("\e[33m Path_stack \e[0m");
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		debug && printf("%s", (*it)?"T":"F" );
	}
	debug && printf("\n");
	

}

bool br_instr_cond(char* _cmp, char* _joints){

	string cmp = string(_cmp);
	vector<string> joints = tokenize(string(_joints), ",");

	if(!check_name(cmp)) assert(0 && "Wrong comparison for break");

	debug && printf("\e[31m conditional_branch_instr %s %s\e[0m. %s %s\n", name(cmp).c_str(),_joints, name(cmp).c_str(), realvalue(cmp).c_str() );

	debug && printf("\e[32m content \e[0m %s\n", content( name(cmp) ).c_str() );



	string real_value_prev = realvalue(cmp);

	//if(solvable_problem())
		//get_values();
	//insert_problem();
	


	if( int pid = fork() ){

		debug && printf("padre pid %d pidhijo %d\n", getpid(), pid); fflush(stdout);

		
		int status;
		waitpid(pid, &status, 0);

		path_stack.push_back( real_value_prev == "true");
		print_path_stack();

		if(yet_covered()) exit(0);

		insert_problem();

		debug && printf("proceso %d acaba de esperar\n", getpid() ); fflush(stdout);

		return real_value_prev == "true";
	} else {


		if( realvalue(cmp) == "true" )
			push_condition( negation(content( name(cmp) )), actual_function, joints );
		else
			push_condition( content( name(cmp) ) , actual_function, joints );


		see_each_problem && show_problem();


		if( solvable_problem() ){
			debug && printf("hijo sat\n"); fflush(stdout);
			get_values();

			path_stack.push_back( real_value_prev != "true");
			print_path_stack();

			if(yet_covered()) exit(0);

			insert_problem();
			debug && printf("fin hijo sat\n"); fflush(stdout);
			return real_value_prev != "true";
		} else {
			debug && printf("hijo unsat\n"); fflush(stdout);
			//insert_problem();
			exit(0);
		}
	}


}

