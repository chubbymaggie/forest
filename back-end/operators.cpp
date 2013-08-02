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

#define debug true
#define see_each_problem false
#define SIZE_STR 512
#define UNDERSCORE "_"
#define PROPAGATE_CONSTANTS true

int alloca_pointer = 0;
vector<pair<string, string> > callstack;

string actual_function;
string actual_bb;

void cast_instruction(char* _dst, char* _src, char* _type){

	string dst = string(_dst);
	string src = string(_src);
	string type = string(_type);


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for cast_instruction");
	if(!check_mangled_name(name(src))) assert(0 && "Wrong src for cast_instruction");


	assign_instruction(src,dst);

	if( get_type(name(src)) != "bool" )
		settype(name(dst), type);
	else
		settype(name(dst), "bool");

	debug && printf("\e[31m Cast_instruction %s %s %s\e[0m. %s %s %s %s\n", name(dst).c_str(), name(src).c_str(), type.c_str(),
		                                                              name(src).c_str(), realvalue(src).c_str(),
		                                                              name(dst).c_str(), realvalue(dst).c_str()  );


}

void NonAnnotatedCallInstr( char* _fn_name, char* _ret_to, char* _ret_type ){

	string fn_name           = string(_fn_name);
	string ret_to            = string(_ret_to);
	string ret_type          = string(_ret_type);

	set_name_hint(name(ret_to), "return of " + fn_name );
	settype(name(ret_to), ret_type );

	printf("\e[31m NonAnnotatedCallInstr %s %s %s\e[0m\n", _fn_name, _ret_to, _ret_type );
}

void CallInstr( char* _fn_name, char* _oplist, char* _fn_oplist, char* _ret_to ){


	string fn_name           = string(_fn_name);
	vector<string> oplist    = tokenize( string(_oplist), ",");
	vector<string> fn_oplist = tokenize( string(_fn_oplist), ",");
	string ret_to            = string(_ret_to);

	myReplace(fn_name, UNDERSCORE, "");



	for ( unsigned int i = 0; i < oplist.size(); i++) {

		assign_instruction( oplist[i], fn_oplist[i], fn_name );

	}



	debug && printf("\e[31m CallInstr %s %s %s %s\e[0m\n", _fn_name, _oplist, _fn_oplist, _ret_to );

	callstack.push_back( pair<string, string>(ret_to, actual_function) );


}

void select_op(char* _dest, char* _cond, char* _sel1, char* _sel2 ){

	string dest = string(_dest);
	string cond = string(_cond);
	string sel1 = string(_sel1);
	string sel2 = string(_sel2);

	if( realvalue(cond) == "true" ){

		assign_instruction( sel1, dest  );

	} else if( realvalue(cond) == "false" ){

		assign_instruction( sel2, dest  );

	} else {
		assert(0 && "Not binary condition");
	}

	debug && printf("\e[31m select_op %s %s %s %s\e[0m\n", _dest, _cond, _sel1, _sel2);
	//exit(0);

}

void ReturnInstr(char* _retname ){

	string retname = string(_retname);

	if(!check_mangled_name(name(retname))) assert(0 && "Wrong return name for ReturnInstr");



	if( callstack.size() == 0 ) return;
	if( retname == "register_" ){

		string last_fn_callstack = callstack[ callstack.size() - 1].second;

		callstack.erase( callstack.end() - 1 );
		actual_function = last_fn_callstack;

		return;
	}

	string last_rg_callstack = callstack[ callstack.size() - 1].first;
	string last_fn_callstack = callstack[ callstack.size() - 1].second;

	assign_instruction( retname, last_rg_callstack, last_fn_callstack );

	callstack.erase( callstack.end() - 1 );
	actual_function = last_fn_callstack;


	debug && printf("\e[31m ReturnInstr %s \e[0m size %lu \n", _retname, callstack.size() );


}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){

	string dst = string(_dst);
	string op1 = string(_op1);
	string op2 = string(_op2);
	string operation = string(_operation);


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for binary_op");
	if(!check_mangled_name(name(op1))) assert(0 && "Wrong op1 for binary_op");
	if(!check_mangled_name(name(op2))) assert(0 && "Wrong op2 for binary_op");


	binary_instruction(dst, op1, op2, operation);

	debug && printf("\e[31m binary_operation %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _op1, _op2, _operation, 
			                                                        op1.c_str(), realvalue(op1).c_str(),
									        op2.c_str(), realvalue(op2).c_str(),
										_dst, realvalue(dst).c_str() );

}

void load_instr(char* _dst, char* _addr){

	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem" UNDERSCORE + realvalue(addr);

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for load");
	if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for load");



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
	string dst = "mem" UNDERSCORE + realvalue(string(_addr)) ;


	if(!check_mangled_name(name(src))) assert(0 && "Wrong src for store");
	if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for store");
	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for store");


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

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for compare");
	if(!check_mangled_name(name(cmp1))) assert(0 && "Wrong cmp1 for compare");
	if(!check_mangled_name(name(cmp2))) assert(0 && "Wrong cmp2 for compare");


	binary_instruction(dst, cmp1, cmp2, type);

	debug && printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(cmp1).c_str(), name(cmp2).c_str(), type.c_str(), 
			                                                 name(cmp1).c_str(), realvalue(cmp1).c_str(),
									 name(cmp2).c_str(), realvalue(cmp2).c_str(),
									 name(dst).c_str(), realvalue(dst).c_str() );

	settype(name(dst), "bool");

	assert( (realvalue(dst) == "true" || realvalue(dst) == "false") && "Invalid result for a comparison operation" );
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

int get_size(string type){

	if( type == "IntegerTyID32" )
		return 4;

	if( type == "DoubleTyID" )
		return 8;

	if( type == "FloatTyID" )
		return 8;

	if( type == "IntegerTyID8" )
		return 1;

	if( type == "IntegerTyID16" )
		return 2;

	if( type == "IntegerTyID64" )
		return 8;

	if( type == "int" )
		return 4;


	if( type.find(",") != string::npos ){
		int sum = 0;
		vector<string> tokens = tokenize(type,",");
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			sum += get_size(*it);
		}
		return sum;
	}


	printf("get_size type %s\n", type.c_str());

	assert(0 && "Unknown type");

}

void global_var_init(char* _varname, char* _type, char* _values){

	string varname        = string(_varname);
	string type           = string(_type);
	vector<string> types = tokenize(string(_type), ",");
	vector<string> values = tokenize(string(_values), ",");

	debug && printf("\e[33m global_var_init %s %s %s\e[0m.\n", _varname, _type, _values);


	if( types.size() != values.size() ){
		printf("%lu %lu\n", types.size(), values.size() );
		assert( 0 && "Different number of types and values");
	}

	if(!check_mangled_name(name(varname))) assert(0 && "Wrong name for global_var_init");


	stringstream rvalue; rvalue << "constant" UNDERSCORE << alloca_pointer; 
	settype( name(varname), "Pointer");
	assign_instruction(rvalue.str(), name(varname));

	stringstream mem_var_aux; mem_var_aux << "mem" UNDERSCORE << itos(alloca_pointer);
	int prev_alloca_pointer = alloca_pointer;

	for ( unsigned int i = 0; i < values.size(); i++) {

		stringstream mem_var; mem_var << "mem" UNDERSCORE << itos(alloca_pointer);

		settype(mem_var.str(), types[i]);

		if(values[i] != "X"){
			stringstream constant_name; constant_name << values[i];

			assign_instruction( constant_name.str(), mem_var.str());
		}

		stringstream hint;
		if(values.size() > 1){
			hint << varname << "+" << (alloca_pointer-prev_alloca_pointer);
		} else {
			hint << varname;
		}

		set_name_hint(mem_var.str(), hint.str());


		alloca_pointer += get_size(types[i]);
	}


	debug && printf("\e[31m global_var_init %s %s %s\e[0m. %s %s %s %s allocapointer %d\n", varname.c_str(),type.c_str(),_values 
			, name(varname).c_str(), realvalue(name(varname)).c_str(), mem_var_aux.str().c_str(), realvalue(mem_var_aux.str()).c_str(), alloca_pointer );
}

void alloca_instr(char* _reg, char* _subtype){

	string reg = string(_reg);
	string subtypes = string(_subtype);
	vector<string> subtype = tokenize(string(_subtype), ",");

	printf("\e[33m alloca_instr \e[0m %s %s\n", _reg, _subtype );

	//exit(0);


	if(!check_mangled_name(name(reg))) assert(0 && "Wrong name for alloca_instr");


	stringstream rvalue; rvalue << "constant" UNDERSCORE << alloca_pointer; 
	settype( name(reg), "Pointer");
	assign_instruction(rvalue.str(), reg );

	stringstream mem_var_aux; mem_var_aux << "mem" UNDERSCORE << itos(alloca_pointer);
	int initial_alloca_pointer = alloca_pointer;

	for ( unsigned int i = 0; i < subtype.size(); i++) {

		stringstream mem_hint;
		stringstream mem_name; mem_name << "mem" UNDERSCORE << itos(alloca_pointer);

		settype(mem_name.str(), subtype[i]);

		if(subtype.size() == 1)
			mem_hint << reg;
		else 
			mem_hint << reg << "+" << alloca_pointer - initial_alloca_pointer;
		set_name_hint(mem_name.str(), mem_hint.str() );

		alloca_pointer += get_size(subtype[i]);
	}

	debug && printf("\e[31m alloca_instr %s %s \e[0m. %s %s %s %s allocapointer %d\n", name(reg).c_str(), subtypes.c_str(), name(reg).c_str(), realvalue(reg).c_str(), mem_var_aux.str().c_str(), realvalue(mem_var_aux.str()).c_str(), alloca_pointer);

}

int get_ini_elem(int nelem_target, string offset_tree){

	int depth = -1;
	int nelem = -1;
	for ( unsigned int i = 1; i < offset_tree.size(); i++) {
		if(offset_tree[i] == '(') depth++;
		if(offset_tree[i] == ')') depth--;
		if(depth == 0 && offset_tree[i] == '(' ){
			nelem++;
			//printf("elem %d at %d\n", nelem, i);
		}
		if(nelem == nelem_target){
			//printf("get_ini_elem %d %s : %d\n", nelem_target, offset_tree.c_str(), i);
			return i;

		}
	}

	assert(0 && "Unbalanced tree");

}

string close_str(string offset_tree){

	int depth = 0;
	for ( unsigned int i = 0; i < offset_tree.size(); i++) {
		if(offset_tree[i] == '(') depth++;
		if(offset_tree[i] == ')') depth--;
		if(depth == 0) return offset_tree.substr(0,i+1);
	}

	assert(0 && "Unbalanced tree");

}

string trimpar(string str){

	int n1 = str.find_first_not_of("()");
	int n2 = str.substr(n1).find_first_not_of("0123456789-");
	string firstnum = str.substr(n1).substr(0,n2);
	//printf("trimpar %s %s %d %d %s\n", str.c_str(), str.substr(n1).c_str(),  n1, n2, str.substr(n1).substr(0,n2).c_str() );
	assert( is_number(firstnum) && "ret is not a number");
	return firstnum;
}

int get_offset(vector<string> indexes, string offset_tree){

	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		debug && printf("\e[33m %s ", it->c_str() );
	} debug && printf(" --- ");
	debug && printf(" offset %s\e[0m\n", offset_tree.c_str() );
	

	string realvalue_index_0_s = realvalue( indexes[0] );

	debug && printf("\e[33m %s %s \e[0m\n", indexes[0].c_str(), realvalue(indexes[0]).c_str() );

	int realvalue_index_0 = stoi(realvalue_index_0_s);

	int ini_elem = get_ini_elem(realvalue_index_0, offset_tree);
	string right_str = offset_tree.substr(ini_elem);
	string elem_str = close_str(right_str);

	vector<string>::iterator first_it = indexes.begin(); first_it++;
	vector<string> rem_indexes = vector<string>(first_it, indexes.end());

	if( rem_indexes.size() )
		return get_offset(rem_indexes, elem_str);
	else
		return stoi(trimpar(elem_str));

}

void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree){

	string dst     = string(_dst);
	string pointer = string(_pointer);
	vector<string> indexes = tokenize(string(_indexes), ",");
	string offset_tree = string(_offset_tree);


	debug && printf("\e[33m getelementptr %s %s %s %s\e[0m. %s %s %s %s\n", dst.c_str(), pointer.c_str(), _indexes,_offset_tree,
		                                                          name(pointer).c_str(), realvalue(pointer).c_str(), 
									  name(dst).c_str(), realvalue(dst).c_str() );


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for getelementptr");
	if(!check_mangled_name(name(pointer))) assert(0 && "Wrong dst for getelementptr");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_mangled_name(name(*it))) assert(0 && "Wrong index for getelementptr");
	}
	

	int offset = get_offset(indexes, offset_tree);
	printf("offset %d\n", offset);
	
	stringstream offset_ss; offset_ss << "constant" UNDERSCORE << offset;
	string offset_constant_s = offset_ss.str();
	
	binary_instruction(dst, pointer, offset_constant_s, "+");
	//exit(0);


	debug && printf("\e[31m getelementptr %s %s %s %s\e[0m. %s %s\n", dst.c_str(), pointer.c_str(), _indexes,_offset_tree,
		                                                          name(dst).c_str(), realvalue(dst).c_str() );

}

void getelementptr_struct(char* _dst, char* _pointer, char* _indexes, char* _offsets){

	string dst     = string(_dst);
	string pointer = string(_pointer);
	vector<string> indexes = tokenize(string(_indexes), ",");
	vector<string> offsets = tokenize(string(_offsets), ",");

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for getelementptr");
	if(!check_mangled_name(name(pointer))) assert(0 && "Wrong dst for getelementptr");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_mangled_name(name(*it))) assert(0 && "Wrong index for getelementptr");
	}
	for( vector<string>::iterator it = offsets.begin(); it != offsets.end(); it++ ){
		if(!check_mangled_name(name(*it))) assert(0 && "Wrong size for getelementptr");
	}
	
	assert( indexes[0] == "constant_0" );
	assert( indexes[1].substr(0,9) == "constant_" );


	int index;
	sscanf( indexes[1].substr(9).c_str(), "%d", &index);

	//printf("%d %s %s\n", index, indexes[index].c_str(), _indexes );

	binary_instruction(dst, pointer, offsets[index], "+");


	
	debug && printf("\e[31m getelementptr_struct %s %s %s %s\e[0m. %s %s\n", dst.c_str(), pointer.c_str(), _indexes, _offsets,
		                                                          name(dst).c_str(), realvalue(dst).c_str() );

}

void begin_sim(){
	debug && printf("\e[31m Begin Simulation\e[0m\n" );
	start_database();
	create_tables();
}

void BeginFn(char* _fn_name){

	string fn_name = string(_fn_name);

	myReplace(fn_name, UNDERSCORE, "");
	actual_function = fn_name;

	myReplace(actual_function, UNDERSCORE, "underscore");


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

bool br_instr_cond(char* _cmp, char* _joints){

	string cmp = string(_cmp);
	vector<string> joints = tokenize(string(_joints), ",");

	if(!check_mangled_name(name(cmp))) assert(0 && "Wrong comparison for break");

	debug && printf("\e[31m conditional_branch_instr %s %s\e[0m. %s %s\n", name(cmp).c_str(),_joints, name(cmp).c_str(), realvalue(cmp).c_str() );

	debug && printf("\e[32m content \e[0m %s\n", content( name(cmp) ).c_str() );



	string real_value_prev = realvalue(cmp);

	//if(solvable_problem())
		//get_values();
	//insert_problem();
	


	if( int pid = fork() ){

		//debug && printf("padre pid %d pidhijo %d\n", getpid(), pid); fflush(stdout);

		
		int status;
		waitpid(pid, &status, 0);

		push_path_stack( real_value_prev == "true");
		print_path_stack();

		if(yet_covered()) exit(0);

		insert_problem();

		debug && printf("\e[31m proceso %d acaba de esperar \e[0m\n", getpid() ); fflush(stdout);

		return real_value_prev == "true";
	} else {

		if( get_is_propagated_constant(cmp) && PROPAGATE_CONSTANTS ) exit(0);


		if( realvalue(cmp) == "true" ){
			push_condition( negation(content( name(cmp) )), actual_function, joints, get_fuzz_constr(name(cmp)) );
		} else {
			push_condition( content( name(cmp) ) , actual_function, joints, get_fuzz_constr(name(cmp)));
		}


		see_each_problem && show_problem();


		if( solvable_problem() ){
			debug && printf("\e[31m hijo sat \e[0m\n"); fflush(stdout);
			get_values();

			push_path_stack( real_value_prev != "true");
			print_path_stack();

			if(yet_covered()) exit(0);

			insert_problem();
			debug && printf("\e[31m fin hijo sat \e[0m\n"); fflush(stdout);
			return real_value_prev != "true";
		} else {
			debug && printf("\e[31m hijo unsat \e[0m\n"); fflush(stdout);
			//insert_problem();
			exit(0);
		}
	}


}

