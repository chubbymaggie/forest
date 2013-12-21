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

#define SIZE_STR 512
#define UNDERSCORE "_"

#define debug true

extern Options* options;
extern Operators* operators;
extern Solver* solver;
extern Database* database;
extern Concurrency* concurrency;

extern map<string, string> map_pos_to_last_store;

Operators::Operators(){

	alloca_pointer = 0;

}
Operators::~Operators(){}

void Operators::cast_instruction(char* _dst, char* _src, char* _type){

	string dst = string(_dst);
	string src = string(_src);
	string type = string(_type);


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for cast_instruction");
	if(!check_mangled_name(name(src))) assert(0 && "Wrong src for cast_instruction");


	solver->assign_instruction(name(src),name(dst));

	if( solver->get_type(name(src)) != "bool" )
		solver->settype(name(dst), type);
	else
		solver->settype(name(dst), "bool");

	debug && printf("\e[31m Cast_instruction %s %s %s\e[0m. %s %s %s %s\n", name(dst).c_str(), name(src).c_str(), type.c_str(),
		                                                              name(src).c_str(), realvalue(src).c_str(),
		                                                              name(dst).c_str(), realvalue(dst).c_str()  );


}


vector<string> oplist_gl;
string ret_to_gl;
string ret_gl;
int callstack_size;



void Operators::pr_callstack(){
	for( vector<pair<string, string> >::iterator it = callstack.begin(); it != callstack.end(); it++ ){
		printf("\e[36m callstack %s %s\e[0m \n", it->first.c_str(), it->second.c_str() );
	}
}


void Operators::BeginFn(char* _fn_name, char* _fn_oplist ){

	string fn_name = string(_fn_name);
	vector<string> fn_oplist = tokenize(_fn_oplist, ",");

	debug && printf("\e[36m begin_fn %s \e[0m\n", _fn_name);


	myReplace(fn_name, UNDERSCORE, "");




	for ( unsigned int i = 0; i < oplist_gl.size(); i++) {

		printf("\e[34m actual %s formal %s\e[0m \n", name(oplist_gl[i]).c_str(), name(fn_oplist[i], fn_name).c_str() );

		solver->assign_instruction(
				name(oplist_gl[i]),
				name(fn_oplist[i], fn_name)
				);

		set_name_hint(name(fn_oplist[i], fn_name), "argument_" + itos(i) + "_" + fn_name );



	}

	actual_function = fn_name;
	myReplace(actual_function, UNDERSCORE, "underscore");

	callstack.push_back( pair<string, string>(ret_to_gl, actual_function) );

	pr_callstack();

}


void Operators::CallInstr_post( char* _fn_name, char* _ret_type ){

	int prev_callstack_size = callstack_size;
	int callstack_size_local = callstack.size();

	//printf("prev_callstack_size %d callstack_size_local %d\n", prev_callstack_size, callstack_size_local);
	
	//printf("prev_name %s name %s\n", callstack[callstack.size()-1].second.c_str(), _fn_name);
	//bool annotated = (prev_callstack_size != callstack_size_local);
	
	string n1 = callstack[callstack.size()-1].second;
	string n2 = string(_fn_name);
	myReplace(n1, UNDERSCORE, "");
	myReplace(n2, UNDERSCORE, "");

	bool annotated = ( n1 == n2 );


	debug && printf("\e[31m CallInstr_post %s %s \e[0m. ret_to_gl %s annotated %d(%s %s) \n", _fn_name, _ret_type, ret_to_gl.c_str(), annotated, n1.c_str(), n2.c_str() );

	pr_callstack();


	if(!annotated){
		NonAnnotatedCallInstr( _fn_name, _ret_type );
		return;
	}


	if( callstack.size() == 0 ){

		debug && printf("\e[36m Empty Call-Stack\e[0m.\n" );
		return;
	};
	if( ret_gl == "register_" ){

		callstack.erase( callstack.end() - 1 );
		string last_fn_callstack = callstack[ callstack.size() - 1].second;

		actual_function = last_fn_callstack;

		return;
	}

	string last_rg_callstack = callstack[ callstack.size() - 1].first;
	callstack.erase( callstack.end() - 1 );
	string last_fn_callstack = callstack[ callstack.size() - 1].second;

	solver->assign_instruction( name(ret_gl), name(last_rg_callstack, last_fn_callstack) );

	actual_function = last_fn_callstack;

	solver->clean_conditions_stack("");
	solver->clean_pivots();

	debug && printf("\e[36m Continuing function %s \e[0m.\n", actual_function.c_str() );








}

map<string, int> nonannotated_call_count;

void Operators::NonAnnotatedCallInstr( char* _fn_name, char* _ret_type ){


	debug && printf("\e[33m NonAnnotatedCallInstr %s %s\e[0m\n", _fn_name, _ret_type );
	string fn_name           = string(_fn_name);
	string ret_to            = ret_to_gl;
	string ret_type          = string(_ret_type);

	//printf("nonannotatedcallinstr %s\n", name(ret_to).c_str());

	if(nonannotated_call_count[fn_name] == 0)
		set_name_hint(name(ret_to), "return_of_" + fn_name );
	else {
		set_name_hint(name(ret_to), "return_of_" + fn_name + "_" + itos(nonannotated_call_count[fn_name]) );
		//solver->insert_variable(name(ret_to), "return_of_" + fn_name );
		for ( unsigned int i = 0; i < nonannotated_call_count[fn_name]; i++) {
			if( i == 0 )
				solver->insert_variable_2(name(ret_to), "return_of_" + fn_name );
			else
				solver->insert_variable_2(name(ret_to), "return_of_" + fn_name + "_" + itos(i) );
		}
	}

	nonannotated_call_count[fn_name]++;


	solver->settype(name(ret_to), ret_type );
	solver->set_comes_from_non_annotated(name(ret_to));

	debug && printf("\e[31m NonAnnotatedCallInstr %s %s\e[0m\n", _fn_name, _ret_type );
}


void Operators::CallInstr( char* _oplist, char* _ret_to ){


	vector<string> oplist    = tokenize( string(_oplist), ",");
	string ret_to = string(_ret_to);
	callstack_size = callstack.size();

	debug && printf("\e[31m CallInstr %s %s\e[0m. \e[36m cs_size %d\e[0m \n", _oplist, _ret_to, callstack_size );

	pr_callstack();

	oplist_gl.clear();
	for ( unsigned int i = 0; i < oplist.size(); i++) {
		debug && printf("\e[31m Saving %s\e[0m\n", oplist[i].c_str() );
		oplist_gl.push_back(oplist[i]);
	}


	ret_to_gl = ret_to;

}

void Operators::ReturnInstr(char* _retname ){

	string retname = string(_retname);

	if(!check_mangled_name(name(retname))) assert(0 && "Wrong return name for ReturnInstr");

	ret_gl = retname;



	debug && printf("\e[31m ReturnInstr %s \e[0m size %lu \n", _retname, callstack.size() );


}

void Operators::select_op(char* _dest, char* _cond, char* _sel1, char* _sel2 ){

	string dest = string(_dest);
	string cond = string(_cond);
	string sel1 = string(_sel1);
	string sel2 = string(_sel2);

	if( realvalue(cond) == "true" ){

		solver->assign_instruction( name(sel1), name(dest)  );

	} else if( realvalue(cond) == "false" ){

		solver->assign_instruction( name(sel2), name(dest)  );

	} else {
		assert(0 && "Not binary condition");
	}

	debug && printf("\e[31m select_op %s %s %s %s\e[0m\n", _dest, _cond, _sel1, _sel2);

}


void Operators::binary_op(char* _dst, char* _op1, char* _op2, char* _operation){

	string dst = string(_dst);
	string op1 = string(_op1);
	string op2 = string(_op2);
	string operation = string(_operation);


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for binary_op");
	if(!check_mangled_name(name(op1))) assert(0 && "Wrong op1 for binary_op");
	if(!check_mangled_name(name(op2))) assert(0 && "Wrong op2 for binary_op");


	solver->binary_instruction(name(dst),name(op1),name(op2),operation);

	debug && printf("\e[31m binary_operation %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _op1, _op2, _operation, 
			                                                        op1.c_str(), realvalue(op1).c_str(),
									        op2.c_str(), realvalue(op2).c_str(),
										_dst, realvalue(dst).c_str() );

}


#define update_store(A,B) concurrency->update_store(A,B);


void Operators::load_instr(char* _dst, char* _addr){

	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem" UNDERSCORE + realvalue(addr);


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for load");
	if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for load");

	//if(options->cmd_option_bool("secuencialize")){
		//database->insert_load(src);
	//}

	solver->assign_instruction(name(src),name(dst));

	debug && printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(addr).c_str(),
								    name(addr).c_str(), realvalue(addr).c_str(),
								    name(src).c_str(), realvalue(src).c_str(),
							            name(dst).c_str(), realvalue(dst).c_str()
								    );
	//exit(0);

}

void Operators::store_instr(char* _src, char* _addr){

	// debug && printf("\e[33m store instruction %s %s\e[0m\n", _src, _addr );


	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem" UNDERSCORE + realvalue(string(_addr)) ;




	if(!check_mangled_name(name(src))) assert(0 && "Wrong src for store");
	if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for store");
	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for store");


	//if(options->cmd_option_bool("secuencialize")){
		//solver->content(name(dst));
	
		//stringstream stack;
		//solver->dump_conditions(stack);
	//}

	//if(options->cmd_option_bool("concurrency")){
		//update_store(dst, solver->content(name(src)));
	//}



	solver->assign_instruction(name(src),name(dst));

	debug && printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",name(src).c_str(), name(addr).c_str(),
			                                           name(src).c_str(), realvalue(src).c_str(),
								   name(addr).c_str(), realvalue(addr).c_str(),
								   name(dst).c_str(), realvalue(dst).c_str() );

}

#undef update_store

void Operators::cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){

	string dst  = string(_dst);
	string cmp1 = string(_cmp1);
	string cmp2 = string(_cmp2);
	string type = string(_type);

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for compare");
	if(!check_mangled_name(name(cmp1))) assert(0 && "Wrong cmp1 for compare");
	if(!check_mangled_name(name(cmp2))) assert(0 && "Wrong cmp2 for compare");


	solver->binary_instruction(name(dst),name(cmp1),name(cmp2), type);

	debug && printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(cmp1).c_str(), name(cmp2).c_str(), type.c_str(), 
			                                                 name(cmp1).c_str(), realvalue(cmp1).c_str(),
									 name(cmp2).c_str(), realvalue(cmp2).c_str(),
									 name(dst).c_str(), realvalue(dst).c_str() );

	solver->settype(name(dst), "bool");

	assert( (realvalue(dst) == "true" || realvalue(dst) == "false") && "Invalid result for a comparison operation" );
}

void Operators::br_instr_incond(){

	debug && printf("\e[31m inconditional_branch_instr\e[0m\n" );

}

void Operators::begin_bb(char* name){
	actual_bb = string(name);

	solver->clean_conditions_stack(actual_bb);

	debug && printf("\e[36m begin_bb %s (fn %s)\e[0m\n", name, actual_function.c_str() );
}

void Operators::end_bb(char* name){
	debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

void Operators::global_var_init(char* _varname, char* _type, char* _values){

	//printf("\e[33m global_var_init %s %s %s\e[0m.\n", _varname, _type, _values); fflush(stdout);

	string varname        = string(_varname);
	string type           = string(_type);
	vector<string> types = tokenize(string(_type), ",");
	vector<string> values = tokenize(string(_values), ",");

	int last_address = alloca_pointer + get_size(type) - get_size(types[types.size()-1]);


	if( types.size() != values.size() ){
		printf("%lu %lu\n", types.size(), values.size() );
		assert( 0 && "Different number of types and values");
	}

	if(!check_mangled_name(name(varname))) assert(0 && "Wrong name for global_var_init");


	stringstream rvalue; rvalue << "constant" UNDERSCORE << alloca_pointer; 
	solver->settype( name(varname), "Pointer");
	solver->assign_instruction(name(rvalue.str()), name(varname));

	stringstream mem_var_aux; mem_var_aux << "mem" UNDERSCORE << itos(alloca_pointer);
	int prev_alloca_pointer = alloca_pointer;

	for ( unsigned int i = 0; i < values.size(); i++) {

		stringstream mem_var; mem_var << "mem" UNDERSCORE << itos(alloca_pointer);

		solver->settype(mem_var.str(), types[i]);

		if(values[i] != "X"){
			stringstream constant_name; constant_name << values[i];

			solver->assign_instruction( name(constant_name.str()), name(mem_var.str()));
		}

		stringstream hint;
		if(values.size() > 1){
			hint << varname << "+" << (alloca_pointer-prev_alloca_pointer);
		} else {
			hint << varname;
		}

		set_name_hint(mem_var.str(), hint.str());

		solver->set_last_address(mem_var.str(), last_address);


		alloca_pointer += get_size(types[i]);
	}

	solver->set_last_address(varname, last_address);

	debug && printf("\e[31m global_var_init %s %s %s\e[0m. %s %s %s %s allocapointer %d last_address %d\n", varname.c_str(),type.c_str(),_values 
			, name(varname).c_str(), realvalue(name(varname)).c_str(), mem_var_aux.str().c_str(), realvalue(mem_var_aux.str()).c_str(), alloca_pointer
		        , last_address );
}

void Operators::alloca_instr(char* _reg, char* _subtype){

	string reg = string(_reg);
	string subtypes = string(_subtype);
	vector<string> subtype = tokenize(string(_subtype), ",");

	//printf("\e[33m alloca_instr \e[0m %s %s\n", _reg, _subtype ); fflush(stdout);

	if(!check_mangled_name(name(reg))) assert(0 && "Wrong name for alloca_instr");


	stringstream rvalue; rvalue << "constant" UNDERSCORE << alloca_pointer; 
	solver->settype( name(reg), "Pointer");
	solver->assign_instruction(name(rvalue.str()), name(reg) );

	stringstream mem_var_aux; mem_var_aux << "mem" UNDERSCORE << itos(alloca_pointer);
	int initial_alloca_pointer = alloca_pointer;

	int last_address = alloca_pointer + get_size(subtypes) - get_size(subtype[subtype.size()-1]);

	for ( unsigned int i = 0; i < subtype.size(); i++) {

		stringstream mem_hint;
		stringstream mem_name; mem_name << "mem" UNDERSCORE << itos(alloca_pointer);

		solver->settype(mem_name.str(), subtype[i]);

		if(subtype.size() == 1)
			mem_hint << actual_function << "_" << reg;
		else 
			mem_hint << actual_function << "_" << reg << "+" << alloca_pointer - initial_alloca_pointer;
		set_name_hint(mem_name.str(), mem_hint.str() );

		solver->set_last_address(name(mem_name.str()), last_address);

		alloca_pointer += get_size(subtype[i]);
	}

	solver->set_last_address(name(reg), last_address);


	debug && printf("\e[31m alloca_instr %s %s \e[0m. %s %s %s %s allocapointer %d last_address %d\n", name(reg).c_str(), subtypes.c_str(), name(reg).c_str(), realvalue(reg).c_str(), mem_var_aux.str().c_str(), realvalue(mem_var_aux.str()).c_str(), alloca_pointer, solver->get_last_address(name(mem_var_aux.str())));
}

void Operators::getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree){

	string dst     = string(_dst);
	string pointer = string(_pointer);
	vector<string> indexes = tokenize(string(_indexes), ",");
	string offset_tree = string(_offset_tree);

	debug && printf("\e[33m getelementptr %s %s %s %s\e[0m. %s %s %s %s\n", dst.c_str(), pointer.c_str(), _indexes,_offset_tree, 
		                                                          name(pointer).c_str(), realvalue(pointer).c_str(), 
									  name(dst).c_str(), realvalue(dst).c_str() );

	//printf("srctree %s\n", get_offset_tree(pointer).c_str() );


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for getelementptr");
	if(!check_mangled_name(name(pointer))) assert(0 && "Wrong dst for getelementptr");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_mangled_name(name(*it))) assert(0 && "Wrong index for getelementptr");
	}

	//if( get_offset_tree(name(pointer)) != "" && offset_tree == "((0))" ){
		//printf("\e[35m Using source offset_tree \e[0m %s\n", get_offset_tree(name(pointer)).c_str() );
		//offset_tree = get_offset_tree(name(pointer));
	//}
	

	string remaining_tree;
	int offset = get_offset(indexes, offset_tree, &remaining_tree);
	solver->set_offset_tree(name(dst), remaining_tree);
	//printf("offset %d remaining_tree %s remaining_tree %s\n", offset, remaining_tree.c_str(), get_offset_tree(dst).c_str() );

	
	stringstream offset_ss; offset_ss << offset;
	string offset_constant_s = offset_ss.str();
	offset_constant_s = "constant_" + offset_constant_s;

	printf("offset_constant_s %s\n", offset_constant_s.c_str());
	
	solver->binary_instruction(name(dst),name(pointer), offset_constant_s, "+");
	//exit(0);



	debug && printf("\e[31m getelementptr %s %s %s %s\e[0m. %s realvalue %s lastaddress %d\n",
			dst.c_str(), pointer.c_str(), _indexes,_offset_tree,
			name(dst).c_str(), realvalue(dst).c_str(), solver->get_last_address(name(pointer)) );

	//assert( stoi(realvalue(dst)) <= solver->get_last_address(name(pointer)) && "Dereference to value out-of-bounds" );
	if( stoi(realvalue(dst)) > solver->get_last_address(name(pointer)) )
		exit(0);

}

void Operators::begin_sim(){
	debug && printf("\e[31m Begin Simulation\e[0m\n" );
	database->start_database();

	options->read_options();
	see_each_problem = options->cmd_option_bool("see_each_problem");
	propagate_constants = options->cmd_option_bool("propagate_constants");
	exit_on_insert = options->cmd_option_bool("exit_on_insert");


	database->create_tables();
	solver->load_forced_free_vars();

	//debug = true;//options->cmd_option_bool("debug");

	//alloca_pointer = 0;
}

void Operators::end_sim(){

	solver->dump_model();
	database->end_database();
	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	
}

bool Operators::br_instr_cond(char* _cmp, char* _joints){

	string cmp = string(_cmp);
	vector<string> joints = tokenize(string(_joints), ",");

	if(!check_mangled_name(name(cmp))) assert(0 && "Wrong comparison for break");

	debug && printf("\e[31m conditional_branch_instr %s %s\e[0m. %s %s\n", name(cmp).c_str(),_joints, name(cmp).c_str(), realvalue(cmp).c_str() );

	debug && printf("\e[32m content \e[0m %s \e[32m prop_constant \e[0m %d \e[32m comes_from_non_annotated\e[0m  %d\n", solver->content( name(cmp) ).c_str(), solver->get_is_propagated_constant(name(cmp)), solver->get_comes_from_non_annotated(name(cmp)) );


	//solver->print_path_stack();


	string real_value_prev = realvalue(cmp);



	if( int pid = fork() ){

		//debug && printf("padre pid %d pidhijo %d\n", getpid(), pid); fflush(stdout);

		
		int status;
		waitpid(pid, &status, 0);

		solver->push_path_stack( real_value_prev == "true");
		solver->print_path_stack();

		//if(yet_covered()) exit(0);

		//solve_problem();
		solver->set_sat(true);
		database->insert_problem();

		if( options->cmd_option_bool("propagate_constants") && solver->get_is_propagated_constant(name(cmp)) )
			return real_value_prev == "true";

		if( realvalue(cmp) == "true" ){
			if( options->cmd_option_bool("cyclotonic") ){
				solver->push_condition(solver->content(name(cmp)));
			} else {
				if(solver->get_comes_from_non_annotated(name(cmp)))
					solver->push_condition(solver->content(name(cmp)));
				else
					solver->push_condition( solver->content( name(cmp) ) , actual_function, joints );
			}
		} else if (realvalue(cmp) == "false" ){
			if( options->cmd_option_bool("cyclotonic") ){
					solver->push_condition( solver->negation(solver->content( name(cmp) )) );
			} else {
				if(solver->get_comes_from_non_annotated(name(cmp)))
					solver->push_condition( solver->negation(solver->content( name(cmp) )) );
				else
					solver->push_condition( solver->negation(solver->content( name(cmp) )), actual_function, joints );
			}
		} else {
			assert(0 && "Non-boolean value for condition");
		}

		debug && printf("\e[31m proceso %d acaba de esperar \e[0m\n", getpid() ); fflush(stdout);

		return real_value_prev == "true";
	} else {

		if( solver->get_is_propagated_constant(name(cmp)) && propagate_constants ) exit(0);

		if( exit_on_insert ){
			system("killall final");
			assert(0 && "exit_on_insert");
		}


		if( realvalue(cmp) == "true" ){
			if( options->cmd_option_bool("cyclotonic") ){
					solver->push_condition( solver->negation(solver->content( name(cmp) )) );
			} else {
				if(solver->get_comes_from_non_annotated(name(cmp)))
					solver->push_condition( solver->negation(solver->content( name(cmp) )) );
				else
					solver->push_condition( solver->negation(solver->content( name(cmp) )), actual_function, joints );
			}
		} else if (realvalue(cmp) == "false" ){
			if( options->cmd_option_bool("cyclotonic") ){
					solver->push_condition( solver->content( name(cmp) ) );
			} else {
				if(solver->get_comes_from_non_annotated(name(cmp)))
					solver->push_condition( solver->content( name(cmp) ) );
				else
					solver->push_condition( solver->content( name(cmp) ) , actual_function, joints );
			}
		} else {
			assert(0 && "Non-boolean value for condition");
		}


		see_each_problem && solver->show_problem();

		solver->solve_problem();

		if( solver->solvable_problem() ){
			debug && printf("\e[31m hijo sat \e[0m\n"); fflush(stdout);

			solver->push_path_stack( real_value_prev != "true");
			solver->print_path_stack();

			//if(yet_covered()) exit(0);

			//solver->solve_problem();
			database->insert_problem();
			debug && printf("\e[31m fin hijo sat \e[0m\n"); fflush(stdout);
			return real_value_prev != "true";
		} else {
			debug && printf("\e[31m hijo unsat \e[0m\n"); fflush(stdout);
			//insert_problem();
			exit(0);
		}
	}


}

void force_free(int* a){

}

void Operators::Free_fn( char* _oplist ){

	string oplist = string(_oplist).substr(0, strlen(_oplist) - 1);

	solver->free_var(name(oplist));
	debug && printf("\e[31m FreeFn %s\e[0m\n", _oplist );

}

string Operators::name( string input, string fn_name ){

	if(input.substr(0,9) != "constant" UNDERSCORE &&
			input.substr(0,4) != "mem" UNDERSCORE &&
	 		input.substr(0,7) != "global" UNDERSCORE &&
			input.substr(0,9) != "function" UNDERSCORE )
		myReplace(input, UNDERSCORE, "underscore" );


	if( input.substr(0,7) == "global" UNDERSCORE ){
		string postfix = input.substr(7);
		//printf("postfix %s\n", postfix.c_str() );
		myReplace(postfix, UNDERSCORE, "underscore");
		input = string("global") + UNDERSCORE + postfix;

		//printf("globalname %s\n", input.c_str());
	}

	if(input.find("constant") != string::npos ){
		return input;
		//int ini = 9;
		//string interm = input.substr(ini);
		//int len = interm.find(UNDERSCORE);
		//string final = interm.substr(0, len);

		//return final;
	} else if (input.substr(0,4) == "mem" UNDERSCORE ){
		return input;
	} else if (input.substr(0,7) == "global" UNDERSCORE ){
		return input;
	} else if (input.find("function") != string::npos ){
		return input;
	} else {
		return ((fn_name == "")?actual_function:fn_name) + UNDERSCORE + input;
		//return input;
	}


}

void Operators::set_name_hint(string name, string hint){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for set_name_hint");
	solver->set_name_hint(name, hint);

}

bool Operators::check_mangled_name(string name){

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
		   tokens[0].substr(0,3) != "mem"      &&
		   tokens[0].substr(0,6) != "global"   &&
		   tokens[0].substr(0,8) != "constant" &&
		   tokens[0].substr(0,8) != "function"
		  ) return false;
	}

	if( number_of_underscore  == 0 ){
		if( !is_number(name) )
			return false;
	}


	return true;

}

string Operators::realvalue(string varname){
	return solver->realvalue(name(varname));
}

int Operators::get_offset(vector<string> indexes, string offset_tree, string* remaining_tree){


	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		debug && printf("\e[33m %s ", it->c_str() );
	} debug && printf(" --- ");
	debug && printf(" offset %s\e[0m\n", offset_tree.c_str() );
	

	string realvalue_index_0_s = realvalue( indexes[0] );

	debug && printf("\e[33m %s %s \e[0m\n", indexes[0].c_str(), realvalue(indexes[0]).c_str() );

	int realvalue_index_0 = stoi(realvalue_index_0_s);

	if( has_index(offset_tree, realvalue_index_0) ){

		int ini_elem = get_ini_elem(realvalue_index_0, offset_tree);
		string right_str = offset_tree.substr(ini_elem);
		string elem_str = close_str(right_str);
		//printf("elem_str %s\n", elem_str.c_str());

		vector<string>::iterator first_it = indexes.begin(); first_it++;
		vector<string> rem_indexes = vector<string>(first_it, indexes.end());

		if( rem_indexes.size() ){
			return get_offset(rem_indexes, elem_str, remaining_tree);
		} else {
			*remaining_tree = offset_tree;
			//printf("elem_str to trim %s\n", elem_str.c_str());
			return stoi(trimpar(elem_str));
		}

	} else {
		vector<string> tokens = tokenize(offset_tree, "(),");
		string size_s = tokens[tokens.size()-1];
		int size = stoi(size_s);
		printf("offset_tree %s realvalue_index_0 %d size_s %s\n", offset_tree.c_str(), realvalue_index_0, size_s.c_str());
		return size*realvalue_index_0;
	}

}

string Operators::get_actual_bb(){

	return actual_bb;

}

string Operators::get_actual_function(){
	return actual_function;
}

void Operators::pivot_variable(char* _varname){

	//string varname = string(_varname).substr(0, strlen(_varname)-1);
	string varname = string(_varname);
	
	varname = name(varname);
	//myReplace(varname, "underscore", "_");

	string hint = solver->get_name_hint(varname);
	string position = solver->get_position(varname);

	//printf("varname %s hint %s position %s\n",varname.c_str(), hint.c_str(), position.c_str() );

	solver->pivot_variable(varname, "hola");

	printf("\e[31m \n pivot_variable %s\e[0m\n", varname.c_str() );

	//string content = solver->content(varname);
	//printf("varname %s\n", varname.c_str() );
	//printf("content %s\n", content.c_str());
	


}

void Operators::pivot_hint(char* _hint){
	string hint = string(_hint);

	string varname = solver->find_by_name_hint(hint);

	solver->pivot_variable(varname, "hola");

	printf("\e[31m \n pivot_hint %s %s\e[0m\n", hint.c_str(), varname.c_str() );

}


