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


#include "solver_wrapper.h"
#include "operators.h"
#include "utils.h"
#include "timer.h"
#include "options.h"
#include "database.h"

#define UNDERSCORE "_"
#define PAUSE_ON_INSERT false
#define EXIT_ON_INSERT false

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

SolverWrapper::SolverWrapper(){

	options->read_options();
	debug = options->cmd_option_bool("verbose");

}

SolverWrapper::~SolverWrapper(){}

void SolverWrapper::free_var(string var){

	if(!check_mangled_name(var)) assert(0 && "Wrong name for content");

	stringstream mem_name; mem_name << "mem_" << variables[var].content;
	forced_free_vars.insert( mem_name.str() );

}

string SolverWrapper::content( string name, string type ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	if(name.find("constant_") != string::npos )
		return internal_representation(name.substr(9),type);

	if( variables[name].content == "" || is_forced_free(name) ){
		string position;
	        if(name.substr(0,7) == "global_")
			position = operators->get_actual_function() + UNDERSCORE + variables[name].name_hint;
		else
			position = variables[name].name_hint;
		insert_variable(name, position );

		if(is_number(name)) return name;
		else return position;
		//return name;

	} else {
		if(get_is_propagated_constant(name))
			return variables[name].real_value;
		else
			return variables[name].content;
	}
}

void SolverWrapper::dump_model(){


	vector<string> outputs = options->cmd_option_vector_str("output");

	debug && printf("\e[32m dump_model %lu \e[0m\n", outputs.size() );

	string free_vars;
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		free_vars += (it->position + ",");
	}
	

	for( vector<string>::iterator it = outputs.begin(); it != outputs.end(); it++ ){

		debug && printf("\e[32m dumping_model %s \e[0m\n", it->c_str() );

		string variable = *it;
		string content_var = content(variable);
		//string path_cond = get_anded_stack_conditions();
		string path_cond = get_comma_stack_conditions();
		database->insert_model_entry(variable, free_vars, content_var, path_cond);
		
	}
	
	
}

void SolverWrapper::set_last_address(string name, int last_address){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_last_address");

	debug && printf("\e[32m set_last_address %s %d \e[0m\n", name.c_str(), last_address);

	variables[name].last_address = last_address;

}

void SolverWrapper::set_first_address(string name, int first_address){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_first_address");

	debug && printf("\e[32m set_first_address %s %d \e[0m\n", name.c_str(), first_address);

	variables[name].first_address = first_address;

}

int SolverWrapper::get_last_address(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for get_last_address");
	return variables[name].last_address;

}

int SolverWrapper::get_first_address(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for get_first_address");
	return variables[name].first_address;

}

void SolverWrapper::show_pivots(){

	//printf("dump pivots\n");

	for( map<string,vector<Pivot> >::iterator it = pivot_variables.begin(); it != pivot_variables.end(); it++ ){

		vector<Pivot> pivots = it->second;

		for( vector<Pivot>::iterator it2 = pivots.begin(); it2 != pivots.end(); it2++ ){
		
			string variable = it2->variable;


			string hintpivot = variable;
			string hint = hintpivot.substr(0, hintpivot.find("_pivot_"));
			string name = find_by_name_hint(hint);
			
			//printf("gettype %s %s\n", name.c_str(), get_type(name).c_str() );
			string type = get_type(name);
			//printf("gettype\n");
			printf("(declare-fun %s () %s)\n", name.c_str(), type.c_str() );
		}
		

	}
	
}

void SolverWrapper::clean_pivots(){

	for( map<string,vector<Pivot> >::iterator it = pivot_variables.begin(); it != pivot_variables.end(); it++ ){

		vector<Pivot> pivots = it->second;

		for( vector<Pivot>::iterator it2 = pivots.begin(); it2 != pivots.end(); it2++ ){

			string function = it2->function;
			if( operators->get_actual_function() != function ){
				pivots.erase( it2 ); it2--;
			}
		}

		it->second = pivots;
	}

}

void SolverWrapper::show_conditions(){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		printf("(assert %s)\n", locknames(it->cond).c_str() );
	}
	
}

string SolverWrapper::find_mem_of_id(string id){


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(it->second.name_hint == id){
			return it->first;
		}
	}

	return "";
	
	

}

void SolverWrapper::dump_conditions( stringstream& sstr ){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		sstr << it->cond;
	}



}

void SolverWrapper::show_check_sat(){


	printf("(check-sat)\n");

}

void SolverWrapper::show_header(){

	printf("(set-option :produce-models true)\n");
	printf("(set-option :pp-decimal true)\n");
	printf("(set-logic AUFNIRA)\n");

}

void SolverWrapper::add_int_constraint(string src){
	if(!check_mangled_name(src)) assert(0 && "Wrong name for add_int_constraint");

	int_constraints.insert(content(src));
}

void SolverWrapper::show_tail(){

	printf("(exit)\n");
}

void SolverWrapper::show_int_constraints(){


	for ( unsigned int i = 0; i < int_constraints.size(); i++) {
		printf( "(declare-fun int_constraint_%d () Int)\n", i);
	}

	unsigned int i = 0;
	for( set<string>::iterator it = int_constraints.begin(); it != int_constraints.end(); it++ ){
		printf( "(assert (= %s int_constraint_%d))\n", it->c_str(), i);
		i++;
	}

}

int SolverWrapper::get_num_fvars(){


	return free_variables.size();

}

string SolverWrapper::result_get(string get_str){


	get_str.erase(get_str.find_last_not_of(" \n\r\t")+1);

	vector<string> tokens = tokenize( get_str, "() ");

	if(tokens.size() < 2){
		printf("%s\n", get_str.c_str() );
		assert(0 && "result_get error");	
	}

	string ret;

	if( tokens[tokens.size() - 2] == "-" )
		ret = "-" + tokens[tokens.size() - 1];
	else 
		ret = tokens[tokens.size() - 1];

	assert( is_number(ret) && "Result is not a number");

	return ret;
}

void SolverWrapper::set_real_value(string varname, string value){


	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	//printf("set_real_value %s %s\n", varname.c_str(), value.c_str());
	variables[varname].real_value = value;
}

void SolverWrapper::set_real_value_mangled(string varname, string value ){


	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[varname].real_value = value;
}

void SolverWrapper::set_real_value_hint(string hint, string value ){



	printf("set_real_value_hint %s %s\n", hint.c_str(), value.c_str());

	
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(it->second.name_hint == hint){
			it->second.real_value = value;
			return;

		}
			
	}

	assert(0 && "Variable not found");
	
}

bool SolverWrapper::get_is_sat(string is_sat){

	if( is_sat == "sat" ) return true;
	else return false;
}

float SolverWrapper::get_solve_time(){
	return spent_time;
}

bool SolverWrapper::solvable_problem(){


	return sat;
	
}

void SolverWrapper::set_sat(bool _sat){

	spent_time = 0;
	sat = _sat;
}

void SolverWrapper::check_name_and_pos(string name, string position){
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		if(it->position == position && it->name != name) assert(0 && "Duplicated entry in free_variables");
		if(it->name == name && it->position != position) assert(0 && "Duplicated entry in free_variables");
	}
	
}

void SolverWrapper::insert_variable(string name, string position){

	if( name == "" ){ printf("Empty name %s\n", name.c_str()); assert(0); }
	if( position == "" ){ printf("Empty position %s\n", position.c_str()); assert(0); }
	if( variables[name].type == "Pointer" ) printf("Pointer_free_variable\n");
	if( variables[name].type == "PointerTyID" ) printf("Pointer_free_variable\n");

	if(!check_mangled_name(name)) assert(0 && "Wrong name for insert_variable");


	if( name.find("constant") != string::npos )
		return;

	if( is_number(name) )
		return;


	if( name.find("function") != string::npos )
		return;

	if( gettype(name) == "Function" )
		return;

	//if(variables[name].contents.size() == 0)
		//return;
		
	debug && printf("\e[35m Insert_variable \e[0m name %s hint %s position %s size %lu\n", name.c_str(), variables[name].name_hint.c_str(), position.c_str(), free_variables.size() );

	if( PAUSE_ON_INSERT )
		getchar();

	if( EXIT_ON_INSERT )
		exit(0);

	//check_name_and_pos(name, position);

	NameAndPosition nandp = {name, position};
	free_variables.insert(nandp);

	//for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
	//	printf("free_variable %s %s\n", it->name.c_str(), it->position.c_str() );
	//}
	

}

void SolverWrapper::push_condition(string cond, bool invert ){

	set<string> joints_set;
	string fn = "";
	Condition condition = { invert?negation(cond):cond, fn, joints_set };

	conditions.push_back( condition );

}

void SolverWrapper::push_condition_static(string cond, bool invert){


	string function = operators->get_actual_function();
	string bb = operators->get_actual_bb();

	if(invert)
		cond = "(not " + cond + ")";

	for ( unsigned int i = 0; i < 10; i++) 
		myReplace(cond, "(not (not ", "");

	string cond_op;
	if(cond.substr(0,6) == "(not ("){
		printf("negate %s %s\n", cond.substr(6,1).c_str(), cond.c_str() );
		cond_op = negateop( cond.substr(6,1) );
	} else {
		cond_op = cond.substr(1,1);
	}

	string condition = function + "_" + bb + "." + cond_op;


	printf("condition_static %s %s %s : %s\n", function.c_str(), bb.c_str(), cond.c_str(), condition.c_str());

	conditions_static.push_back( condition );

}

void SolverWrapper::save_state(){
	path_stack_save        = path_stack;
	conditions_static_save = conditions_static;
	conditions_save        = conditions;
}

void SolverWrapper::load_state(){
	path_stack        = path_stack_save;
	conditions_static = conditions_static_save;
	conditions        = conditions_save;
}

void SolverWrapper::push_condition(string name, string actual_function, vector<string> joints, bool invert){

	if( (!invert && realvalue(name) == "true") || (invert && realvalue(name) == "false") ){
		if( options->cmd_option_bool("cyclotonic") ){
			push_condition(content(name));
		} else {
			if(get_comes_from_non_annotated(name)){
				push_condition(content(name));
			} else {
				push_condition(content(name), actual_function, joints );
			}
		}
	} else if( (!invert && realvalue(name) == "false") || (invert && realvalue(name) == "true") ){
		if( options->cmd_option_bool("cyclotonic") ){
			push_condition(negation(content(name)));
		} else {
			if(get_comes_from_non_annotated(name)){
				push_condition(negation(content(name)));
			} else {
				push_condition(negation(content(name)), actual_function, joints );
			}
		}
	} else {
		assert(0 && "Non-boolean value for condition");
	}
}

void SolverWrapper::push_condition(string cond, string fn, vector<string> joints ){

	//printf("condition comes_from_non_annotated %d\n", get_comes_from_non_annotated(cond) );


	set<string> joints_set = set<string>(joints.begin(), joints.end());

	Condition condition = { cond, fn, joints_set };
	conditions.push_back( condition );
}

string SolverWrapper::negation(string condition){


	stringstream negation_ss;
	negation_ss << "(not " << string(condition) << ")";

	return negation_ss.str();
}

string SolverWrapper::negateop(string predicate){

	if( predicate == "="  ) return "#";
	if( predicate == ">"  ) return "<=";
	if( predicate == ">=" ) return "<";
	if( predicate == "<"  ) return ">=";
	if( predicate == "<=" ) return ">";
	if( predicate == "#"  ) return "=";
	assert(0 && "Unknown Operation");

}

string SolverWrapper::name_without_suffix( string name ){


	if(!check_mangled_name(name)) assert(0 && "Wrong name for name_without_suffix");

	int s1 = name.find(UNDERSCORE);
	int s2 = name.find(UNDERSCORE, s1+1);
	return name.substr(0,s2);
}

string SolverWrapper::get_sized_type(string name){


	if( !check_mangled_name(name) ) assert(0 && "Wrong name for sized type");

	if (variables[name].type == "IntegerTyID32")
		return "Int32";

	if (variables[name].type == "IntegerTyID64")
		return "Int64";

	if (variables[name].type == "IntegerTyID8")
		return "Int8";

	if (variables[name].type == "IntegerTyID16")
		return "Int16";

	if (variables[name].type == "FloatTyID")
		return "Float32";

	if (variables[name].type == "DoubleTyID")
		return "Float64";

	if (variables[name].type == "Int")
		return "Int";

	if (variables[name].type == "PointerTyID")
		return "Pointer";

	if (variables[name].type == "Pointer")
		return "Pointer";


	printf("name %s type %s\n", name.c_str(), variables[name].type.c_str() );

	//fprintf(stderr, "type %s\n", variables[name].type.c_str());
	assert(0 && "Unknown Type");

	return "Int";

}

void SolverWrapper::set_comes_from_non_annotated(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for set_comes_from_non_annotated");

	debug && printf("\e[32m set_comes_from_non_annotated \e[0m %s \n", name.c_str() );

	variables[name].comes_from_non_annotated = true;
	
	
}

bool SolverWrapper::get_comes_from_non_annotated(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for get_comes_from_non_annotated");

	return variables[name].comes_from_non_annotated;
	
	
}

void SolverWrapper::clean_conditions_stack(string name){

	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){

		if( it->joints.size() == 0 && it->function == "" ){
			continue;
		}

		if( it->joints.size() == 0 && operators->get_actual_function() != it->function ){
			debug && printf("\e[35m Erase condition from stack \e[0m %s\n", it->cond.c_str() );
			conditions.erase(it); it--; continue;
		}

		if( it->joints.find(name) != it->joints.end() && operators->get_actual_function() == it->function ){
			debug && printf("\e[35m Erase condition from stack \e[0m %s\n", it->cond.c_str() );
			conditions.erase(it); it--; continue;
		}
	}
	

}

string SolverWrapper::realvalue_mangled(string varname){


	//printf("\e[33m realvalue_mangled \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for realvalue_mangled");


	if( varname.find("constant") != string::npos ){
		return varname.substr(9);
	} else if( variables[varname].real_value == "" ){
		return "0";
	} else {
		return variables[varname].real_value;
	}
}

string SolverWrapper::realvalue(string varname){


	//printf("\e[33m realvalue \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for realvalue");

	if(is_number(varname)){
		return varname;
	} else if( varname.find("constant") != string::npos ){
		//printf("constant\n");
		return varname.substr(9);
	} else if( variables[varname].real_value == "" ){
		//printf("empty\n");
		return "0";
	}else{
		//printf("else\n");
		if( variables.find(varname) == variables.end() ){
			assert(0 && "Variable not found");
		}
		return variables[varname].real_value;
	}

}

void SolverWrapper::set_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for set_is_propagated_constant");

	variables[varname].is_propagated_constant = true;

}

void SolverWrapper::unset_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for unset_is_propagated_constant");

	variables[varname].is_propagated_constant = false;

}

bool SolverWrapper::is_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for is_constant");

	return varname.substr(0,9) == "constant" UNDERSCORE;

}

void SolverWrapper::setcontent(string varname, string content){


	debug && printf("\e[32m setcontent %s %s\e[0m.\n", varname.c_str(), content.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for setcontent");
	variables[varname].content = content;
}

bool SolverWrapper::is_forced_free(string position, bool colateral_effect){

	if(colateral_effect){

		if(!check_mangled_name(position)) assert(0 && "Wrong src for is_forced_free");

		if( forced_free_vars.find(position) != forced_free_vars.end() ){
			if( already_forced_free.find(position) != already_forced_free.end() ){
				return false;
			} else{
				already_forced_free.insert(position);
				return true;
			}
		} else {
			return false;
		}

	} else {

		if(!check_mangled_name(position)) assert(0 && "Wrong src for is_forced_free");

		if( forced_free_vars.find(position) != forced_free_vars.end() ){
			return true;
		} else {
			return false;
		}

	}
}

void SolverWrapper::load_forced_free_vars(){


	ifstream input("free_vars");
	string line;
	
	while( getline( input, line ) ) {
		forced_free_vars.insert(line);
	}
	
}

void SolverWrapper::set_first_content(string src, string content){

	printf("\e[36m set_first_content %s %s\e[0m\n", src.c_str(), content.c_str());

	first_content[src] = content;

}

void SolverWrapper::set_first_content_value(string var, string value){
	printf("\e[36m set_first_content_value %s %s\e[0m\n", var.c_str(), value.c_str() );
	first_content_value[var] = value;
}

string SolverWrapper::get_first_content_value(string var){
	return first_content_value[var];
}

string SolverWrapper::get_first_content(string src){

	return first_content[src];

}

void SolverWrapper::propagate_unary(string src, string dst, bool forcedfree){

	//bool forcedfree = is_forced_free(src);

	if( (get_is_propagated_constant(src) || is_constant(src)) && !forcedfree )
		set_is_propagated_constant(dst);
	else
		unset_is_propagated_constant(dst);


	//printf("srctree %s\n", get_offset_tree(src).c_str());

	set_offset_tree(dst, get_offset_tree(src));

	set_last_address(dst, get_last_address(src));
	set_first_address(dst, get_first_address(src));

	if(get_comes_from_non_annotated(src))
		set_comes_from_non_annotated(dst);

	variables[dst].idx_values = variables[src].idx_values;
	
	init_indexes(dst, src);

}

bool SolverWrapper::implemented_operation(string operation){

	if(operation == "<=") return true;
	if(operation == "u<=") return true;
	if(operation == ">=") return true;
	if(operation == "<" ) return true;
	if(operation == ">" ) return true;
	if(operation == "=" ) return true;
	if(operation == "#" ) return true;
	if(operation == "+" ) return true;
	if(operation == "-" ) return true;
	if(operation == "*" ) return true;
	if(operation == "/" ) return true;
	if(operation == "%" ) return true;
	if(operation == "R" ) return true;
	if(operation == "L" ) return true;
	if(operation == "Y" ) return true;
	if(operation == "O" ) return true;
	if(operation == "X" ) return true;

	printf("operation %s\n", operation.c_str());
	return false;
}

void SolverWrapper::propagate_binary(string op1, string op2, string dst){

	unset_is_propagated_constant(dst);

	if( get_is_propagated_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( get_is_propagated_constant(op1) && is_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( is_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	set_last_address(dst, get_last_address(op1));
	set_first_address(dst, get_first_address(op1));

	if( get_comes_from_non_annotated(op1) )
		set_comes_from_non_annotated(dst);

	if( get_comes_from_non_annotated(op2) )
		set_comes_from_non_annotated(dst);


	variables[dst].idx_values = variables[op1].idx_values;
	
	init_indexes(dst, op1, op2);


}

bool SolverWrapper::is_free_var(string name){
	if(!check_mangled_name(name)) assert(0 && "Wrong name for is_free_var");

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		if(it->name == name) return true;
	}

	return false;
	
}

void SolverWrapper::init_indexes(string dst, string op1, string op2){

	if(!check_mangled_name(dst)) assert(0 && "Wrong name for init_indexes");
	if(!check_mangled_name(op1)) assert(0 && "Wrong name for init_indexes");
	if( op2 != "" && !check_mangled_name(op2)) assert(0 && "Wrong name for init_indexes");

	//printf("variables[%s].indexes.size = %lu\n", op1.c_str(), variables[op1].indexes.size());

	if(is_free_var(op1)){
		variables[dst].indexes.insert(op1);
		debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), op1.c_str());
	}
	set<string> idx_1 = variables[op1].indexes;

	//printf("idx_size %lu\n", idx_1.size());

	for( set<string>::iterator it = idx_1.begin(); it != idx_1.end(); it++ ){
		variables[dst].indexes.insert(*it);
		debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), it->c_str());
	}

	if(op2 != ""){
		if(is_free_var(op2)){
			variables[dst].indexes.insert(op2);
			debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), op2.c_str());
		}

		set<string> idx_2 = variables[op2].indexes;

		for( set<string>::iterator it = idx_2.begin(); it != idx_2.end(); it++ ){
			variables[dst].indexes.insert(*it);
			debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), it->c_str());
		}
	}

	//printf("variables[%s].indexes.size = %lu\n", dst.c_str(), variables[dst].indexes.size());
	
}

int SolverWrapper::show_problem(){


	options->read_options();
	
	if(!options->cmd_option_bool("show_only_constraints")){
	show_header();
	show_pivots();}
	show_int_constraints();
	show_conditions();
	if(!options->cmd_option_bool("show_only_constraints")){
	show_check_sat();
	show_tail();}


	fflush(stdout);

	//getchar();
}

string SolverWrapper::get_offset_tree( string varname ){

	//assert(check_mangled_name(varname) && "Incorrect name for get_offset_tree");
	//printf("get_offset_tree %s %s\n", varname.c_str(), variables[varname].tree.c_str() );
	return variables[varname].tree;
}

bool SolverWrapper::check_mangled_name(string name){

	//printf("check_mangled_name %s\n", name.c_str());

	if(name.find("pivot") != string::npos) return true;

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
		   tokens[0].substr(0,8) != "constant"   && 
		   tokens[0].substr(0,8) != "function"
		  ) return false;
	}

	if( number_of_underscore  == 0 ){
		if( !is_number(name) )
			return false;
	}

	if( number_of_underscore  == 6 ){
		if(name.find("pivot") == string::npos)
			return false;
	}

	return true;

}

bool SolverWrapper::get_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for get_is_propagated_constant");
	if(is_forced_free(varname, false)) return false;
	return variables[varname].is_propagated_constant;
}

string SolverWrapper::gettype(string name){

	//printf("gettype %s\n", name.c_str());

	if( variables.find(name) == variables.end() ) assert(0 && "Not such variable");

	if(name.find("_pivot_") != string::npos)
		name = name.substr(0, name.find("_pivot_"));

	return variables[name].type;
}

void SolverWrapper::set_name_hint(string name, string hint){

	debug && printf("\e[35m set_name_hint \e[0m name %s hint %s \n", name.c_str(), hint.c_str() );

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_name_hint");

	variables[name].name_hint = hint;
}

string SolverWrapper::get_name_hint(string name){

	//debug && printf("\e[33m get_name_hint %s %s\e[0m\n", name.c_str(), variables[name].name_hint.c_str() );

	return variables[name].name_hint;
}

string SolverWrapper::find_by_name_hint(string hint){

	myReplace(hint, "underscore", "_");
	string suffix = hint.substr(hint.find("_") + 1);
	string prefix = hint.substr(0,hint.find("_"));
	myReplace(suffix, "_", "underscore");
	hint = prefix + "_" + suffix;

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		//printf("find_by_name_hint %s %s %s\n", it->first.c_str(), it->second.name_hint.c_str(), it->second.content.c_str() );

		//if(it->second.name_hint == hint )
		if(it->first == hint)
			return it->first;
	}
	
	printf("hint not found %s\n", hint.c_str());
	assert(0 && "name not found");

	return "";
	
}

void SolverWrapper::set_offset_tree( string varname, string tree ){

	//assert(check_mangled_name(varname) && "Incorrect name for set_offset_tree");
	//printf("set_offset_tree %s %s\n", varname.c_str(), tree.c_str() );
	variables[varname].tree = tree;
}

void SolverWrapper::settype(string name, string type){

	// debug && printf("\e[32m Settype \e[0m. %s %s\n", name.c_str(), type.c_str() );

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for settype");
	variables[name].type = type;

}

string SolverWrapper::get_type(string name){

	//printf("get_type %s\n", name.c_str());

	if(name.find("pivot") != string::npos)
		name = name.substr(0,name.find("_pivot_"));

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for type");

	if(name.substr(0,8) == "function"){
		return "Function";
	}

	if(name.substr(0,9) == "constant" UNDERSCORE) return "IntegerTyID32";
	if( is_number(name) ){

		if( name.find(".") != string::npos )
			return "FloatTyID";
		else
			return "IntegerTyID32";
	}

	if (gettype(name) == "IntegerTyID32")
		return "Int";

	if (gettype(name) == "DoubleTyID")
		return "Real";

	if (gettype(name) == "IntegerTyID64")
		return "Int";

	if (gettype(name) == "IntegerTyID8")
		return "Int";

	if (gettype(name) == "IntegerTyID16")
		return "Int";

	if (gettype(name) == "PointerTyID")
		return "Int";

	if (gettype(name) == "Int")
		return "Int";

	if (gettype(name) == "FloatTyID")
		return "Real";

	if (gettype(name) == "Real")
		return "Real";

	if (gettype(name) == "bool")
		return "bool";

	if (gettype(name) == "Pointer")
		return "Pointer";

	if (gettype(name) == "Function")
		return "Function";


	printf("name %s type %s\n", name.c_str(), gettype(name).c_str() );

	assert(0 && "Unknown Type");

	return "Int";

}

vector<bool> SolverWrapper::get_path_stack(){

	return path_stack;
}

string SolverWrapper::get_path_stack_str(){

	string ret;
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		if(*it)
			ret += "T";
		else
			ret += "F";
	}
	
	return ret;
}

void SolverWrapper::push_path_stack(bool step){

	path_stack.push_back(step);
}

void SolverWrapper::print_path_stack(){



	printf("\e[33m Path_stack \e[0m");
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		printf("%s", (*it)?"T":"F" );
	}
	printf("\n");

	printf("\e[33m Depth \e[0m %lu\n", path_stack.size());
	

}

map<string, Variable> SolverWrapper::get_map_variables(){

	return variables;
}

string SolverWrapper::get_anded_stack_conditions(){

	stringstream ret;

	ret << "(and ";
	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		string condition = it->cond;
		ret << condition << " ";
	}

	ret << ")";

	return ret.str();
	

}

string SolverWrapper::get_comma_stack_conditions(){

	stringstream ret;

	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		string condition = it->cond;
		ret << condition << ",";
	}


	return ret.str();
	

}

string SolverWrapper::get_comma_stack_conditions_static(){

	stringstream ret;

	for( vector<string>::iterator it = conditions_static.begin(); it != conditions_static.end(); it++ ){
		string condition = *it;
		ret << condition << ",";
	}


	return ret.str();

}

vector<Condition> SolverWrapper::get_stack_conditions(){

	return conditions;
}

set<NameAndPosition> SolverWrapper::get_free_variables(){
	return free_variables;
}

string SolverWrapper::get_position(string name){


	return variables[name].name_hint;

}

void SolverWrapper::pivot_variable(string variable, string name){


	myReplace(variable, "underscore", "_");
	string suffix = variable.substr(variable.find("_") + 1);
	string prefix = variable.substr(0,variable.find("_"));
	myReplace(suffix, "_", "underscore");

	variable = prefix + "_" + suffix;

	printf("pivot %s %s %s\n", prefix.c_str(), suffix.c_str(), variable.c_str());
	

	debug && printf("\e[33m pivot_variable %s %s\e[0m\n", variable.c_str(), name.c_str());

	string origname = variable;
	string orig_content = content(origname);

	string hint = get_name_hint(variable);

	string pivot_name = hint + "_pivot_" + name;
	setcontent(pivot_name, origname);
	setcontent(origname,orig_content);
	
	vector<string> empty;
	stringstream condition; condition << "(= " << variable << " " << orig_content << ")";
	push_condition(condition.str(), operators->get_actual_function(), empty);

	Pivot pivot = { variable, operators->get_actual_function() };

	pivot_variables[variable].push_back(pivot);


	debug && printf("\e[31m pivot_variable %s %s\e[0m %s %s %s\n", variable.c_str(), name.c_str(), origname.c_str(), orig_content.c_str(), variables[origname].content.c_str() );
}

vector<int> SolverWrapper::jump_offsets(string offset_tree){

	vector<int> ret;

	for ( unsigned int i = 1; offset_tree[i] == '('; i++) {
		string sub = close_str(offset_tree.substr(i));
		string right = sub.substr(sub.find_last_of(","));
		string center = right.substr(1,right.length()-2);
		//printf("sub %s %s\n", sub.c_str(), center.c_str() );
		ret.push_back(stoi(center));
	}

	return ret;
}

void SolverWrapper::add_range_index(string dst, map<set<pair<string, int> > , int > map_idx_val ){

	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for add_range_index");

	printf("add_range_index %s\n", dst.c_str());

	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > idx_vals = it->first;
		int val2 = it->second;
		for( set<pair<string, int> >::iterator it2 = idx_vals.begin(); it2 != idx_vals.end(); it2++ ){
			string idx = it2->first;
			int    val = it2->second;
			printf("idx_vals %s %d %d\n", idx.c_str(), val, val2);
		}
		
	}
	
	variables[dst].idx_values = map_idx_val;

	//pair<int, int> range = pair<int, int>(first_address, last_address);
	//pair<string, pair<int, int> > expr_and_range = pair<string, pair<int, int> >(expr, range);
	//variables[dst].range_indexes.push_back(expr_and_range);

}

void SolverWrapper::add_indexes(string dst, vector<string> indexes){
	if(!check_mangled_name(dst)) assert(0 && "wrong name for add_indexes");

	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		variables[dst].indexes.insert(*it);
	}
	

}

void SolverWrapper::pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base){

	if(!check_mangled_name(dst)) assert(0 && "wrong name for pointer_instruction");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_mangled_name(*it)) assert(0 && "wrong name for pointer_instruction");
	}
	


	debug && printf("\e[32m pointer_instruction %d\e[0m\n", indexes.size() ); fflush(stdout);

	vector<int> jmp_offsets = jump_offsets(offset_tree);

	assert( jmp_offsets.size() == indexes.size() );


	int first_address = get_first_address(base);
	int last_address = get_last_address(base);
	

	string expr = "(+ " + content(base) + " ";
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		stringstream subexpr;
		subexpr << "(* " << content(indexes[i]) << " " << jmp_offsets[i] << ") ";
		expr += subexpr.str();
	}
	expr += ")";


	int real_pointer = stoi(realvalue(base));
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		// printf("rvii %s %s\n", indexes[i].c_str(), realvalue(indexes[i]).c_str() );
		real_pointer += (stoi(realvalue(indexes[i])) * jmp_offsets[i]);
	}
	// printf("real_pointer %d\n", real_pointer);


	
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		init_indexes(dst, indexes[i]);
	}

	map<set<pair<string, int> > , int > map_idx_val = get_idx_val(base,expr, indexes, first_address, last_address);



	setcontent(dst, expr);
	set_real_value(dst, itos(real_pointer));

	bool forcedfree = is_forced_free(base);
	propagate_unary(base, dst, forcedfree);

	add_range_index(dst, map_idx_val);
	add_indexes(dst, indexes);

	//printf("range_index %d\n", variables[dst].idx_values.size() );
	settype(dst, "Pointer");

	debug && printf("\e[32m pointer_instruction \e[0m  expr %s last_addr %d first_addr %d last_addr %d first_addr %d range_index %d\n",
			expr.c_str(),
			get_last_address(base), get_first_address(base),
			get_last_address(dst) , get_first_address(dst),
			variables[dst].idx_values.size()
			);

	//exit(0);

}

set<set<pair<string, int> > > SolverWrapper::get_exclusions( map<set<pair<string, int> > , int > solutions ){

	set<set<pair<string, int> > > ret;
	
	for( map<set<pair<string, int> > , int >::iterator it = solutions.begin(); it != solutions.end(); it++ ){
		set<pair<string, int> > sol = it->first;
		ret.insert(sol);
	}

	return ret;
	

}

map<set<pair<string, int> > , int > SolverWrapper::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){

	debug && printf("\e[32m get_idx_val %s %d %d %d\e[0m\n", base.c_str(), first_address, last_address, indexes.size());
	


	set<string> index_vars = variables[base].indexes;
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		debug && printf("\e[32m index \e[0m %s\n", it->c_str());

		set<string> indexes_index = variables[*it].indexes;
		for( set<string>::iterator it2 = indexes_index.begin(); it2 != indexes_index.end(); it2++ ){
			debug && printf("\e[32m index2 \e[0m %s\n", variables[*it2].name_hint.c_str() );
			index_vars.insert( variables[*it2].name_hint );
		}
	}
	
	map<set<pair<string, int> > , int > ret;

	bool is_sat;

	string idx_show;
	for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
		idx_show += *it + ",";
	}
	

	
	printf("\e[32m base \e[0m %s \e[32m idx_content \e[0m %s \e[32m indexes \e[0m %s \e[32m first_address \e[0m %d \e[32m last_address \e[0m %d\n", base.c_str(), idx_content.c_str(), idx_show.c_str(), first_address, last_address);

	int iters = 0;
	while(true){


		FILE* ftmp = fopen("/tmp/forest/idx_problem.smt2", "w");
		fprintf(ftmp, "(set-option :produce-models true)\n");
		fprintf(ftmp, "(set-logic AUFNIRA)\n");

		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			fprintf(ftmp, "(declare-fun %s () Int)\n", it->c_str());
		}

		stringstream excl_expr;
		stringstream range_expr;

		range_expr << "(and " << "(<= " << first_address << " " << idx_content << " " << last_address << ") " << "(<= " << idx_content << " " << last_address << "))";


		set<set<pair<string, int> > > exclusions = get_exclusions(ret);

		//printf("exclusions.size() %d\n", exclusions.size() );

		excl_expr << "(not ";
		if(exclusions.size() > 1)
			excl_expr << "(or ";
		for( set<set<pair<string, int> > >::iterator it = exclusions.begin(); it != exclusions.end(); it++ ){
			set<pair<string, int> > fsol = (*it);
			if(fsol.size() > 1)
				excl_expr << "(and ";
			for( set<pair<string, int> >::iterator it2 = fsol.begin(); it2 != fsol.end(); it2++ ){
				excl_expr << "(= " << it2->first << " " << it2->second << ") ";
			}
			if(fsol.size() > 1)
				excl_expr << ")";
		}
		if(exclusions.size() > 1)
			excl_expr << ")";
		excl_expr << ")";



		fprintf(ftmp, "(assert %s)\n", range_expr.str().c_str());

		if(exclusions.size() > 0)
			fprintf(ftmp, "(assert %s)\n", excl_expr.str().c_str());






		fprintf(ftmp, "(check-sat)\n");

		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			fprintf(ftmp, "(get-value (%s))\n", it->c_str());
		}

		fprintf(ftmp, "(get-value (%s))\n", idx_content.c_str() );

		fclose(ftmp);

		system("z3 /tmp/forest/idx_problem.smt2 > /tmp/forest/idx_out");


		ifstream input("/tmp/forest/idx_out");
		string line;
		vector<string> result;

		while( getline( input, line ) ) {
			result.push_back(line);
		}


		if(result[0].find("error") != string::npos ){
			printf("Error in z3 execution\n");
			solve_problem();
			assert(0 && "Error in z3 execution");
		}


		is_sat = (result[0] == "sat");

		if(!is_sat){
			//printf("no sat\n");
			break;
		}

		if(iters++ == options->cmd_option_int("max_pointer_deref_combs")){
			//printf("number of iterations exceeded\n");
			break;
		}

		set<pair<string, int> > sub_sol;

		int i = 0;
		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			i++;
			string line = result[i];
			if(line.find("error") != string::npos )
				assert(0 && "Error in z3 execution");

			string varname = *it;
			string value = result_get(line);

			sub_sol.insert(pair<string, int>(varname, stoi(value)));

		}
		
		i++;
		line = result[i];
		int idx_res = stoi(result_get(line));

		//printf("idx_res %d\n", idx_res);

		ret[sub_sol] = idx_res;

		//static int p;
		//if(p++ == 3) break;

	}

	//for( set<pair<string, int> >::iterator it = sub_sol.begin(); it != sub_sol.end(); it++ ){
		//printf("sub_sol %s %d\n", it->first.c_str(), it->second);
	//}
	
	
	return ret;
	//exit(0);

}

string SolverWrapper::get_idx_type(string addr){

	printf("\e[32m get_idx_type %s \e[0m\n", addr.c_str());

	return get_type( "mem_" + itos(variables[addr].idx_values.begin()->second ));

}

bool SolverWrapper::get_outofbounds(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for get_outofbounds");

	return variables[varname].outofbounds;
}

void SolverWrapper::set_outofbounds(string varname, bool outofbounds){

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for get_outofbounds");

	variables[varname].outofbounds = outofbounds;
}

void SolverWrapper::sym_load(string dst, string addr){

	if(!check_mangled_name(dst)) assert(0 && "Wrong name for sym_load");
	if(!check_mangled_name(addr)) assert(0 && "Wrong name for sym_load");

	string idx_content = content(addr);




	stringstream result_expr;

	map<set<pair<string, int> > , int > map_idx_val = variables[addr].idx_values;

	debug && printf("\e[31m sym_load %s %s %d\e[0m\n", dst.c_str(), addr.c_str(), map_idx_val.size() );


	vector<string> mem_names;

	int m = 0;
	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > elem_idx_val = it->first;
		int val = it->second;

		stringstream and_expr;

		if(elem_idx_val.size() > 1){
			and_expr << "(and ";
		}
		for( set<pair<string, int> >::iterator it2 = elem_idx_val.begin(); it2 != elem_idx_val.end(); it2++ ){
			pair<string, int> elem = (*it2);
			string idx = elem.first;
			int idx_val = elem.second;
			
			and_expr << "(= " << idx << " " << idx_val << ")";
		}
		if(elem_idx_val.size() > 1){
			and_expr << ")";
		}

		string mem_val = content("mem_" + itos(val));


		mem_names.push_back("mem_" + itos(val));

		result_expr << "(ite " << and_expr.str() << " " << mem_val << " ";
		m++;
	}
	result_expr << "0";
	for ( unsigned int i = 0; i < m; i++) {
		result_expr << ")";
	}

	setcontent(dst, result_expr.str());

	unset_is_propagated_constant(dst);

	m = 0;
	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > elem_idx_val = it->first;
		int val = it->second;

		for( set<pair<string, int> >::iterator it2 = elem_idx_val.begin(); it2 != elem_idx_val.end(); it2++ ){
			pair<string, int> idxv = (*it2);
			printf("symload %s %d %d %s %s\n", idxv.first.c_str(), idxv.second, val,mem_names[m].c_str(), content(mem_names[m]).c_str() );
		}
		m++;
	}





	load_idx_vals(dst, map_idx_val);

	string type = get_idx_type(addr);
	settype(dst, type );


	
	int actual_addr = stoi(realvalue(addr));
	string actual_value = realvalue("mem_" + itos(actual_addr));

	set_real_value(dst, actual_value);

	printf("\e[32m Variable_load \e[0m dst %s content %s result_expr %s actual_addr %d actual_value %s\n", dst.c_str(), idx_content.c_str(),result_expr.str().c_str(),
			actual_addr, actual_value.c_str() );

	//exit(0);

}

void SolverWrapper::sym_store(string src, string addr){

	if(!check_mangled_name(src)) assert(0 && "Wrong name for sym_store");
	if(!check_mangled_name(addr)) assert(0 && "Wrong name for sym_store");

	string idx_content = content(addr);
	string src_content = content(src);


	map<set<pair<string, int> > , int > map_idx_val = variables[addr].idx_values;

	debug && printf("\e[31m sym_store %s %s %d\e[0m\n", src.c_str(), addr.c_str(), map_idx_val.size() );


	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){

		stringstream result_expr;

		set<pair<string, int> > elem_idx_val = it->first;
		int val = it->second;

		stringstream and_expr;

		if(elem_idx_val.size() > 1){
			and_expr << "(and ";
		}
		for( set<pair<string, int> >::iterator it2 = elem_idx_val.begin(); it2 != elem_idx_val.end(); it2++ ){
			pair<string, int> elem = (*it2);
			string idx = elem.first;
			int idx_val = elem.second;
			
			and_expr << "(= " << idx << " " << idx_val << ")";
		}
		if(elem_idx_val.size() > 1){
			and_expr << ")";
		}

		string mem_name = "mem_" + itos(val);
		string mem_val = content(mem_name);

		result_expr << "(ite " << and_expr.str() << " " << src_content << " " << mem_val << ")";

		debug && printf("\e[32m sym_store \e[0m mem_%d %s\n", val, result_expr.str().c_str() );

		setcontent(mem_name, result_expr.str());

		string type = get_type(src);
		settype(mem_name, type);

		unset_is_propagated_constant(mem_name);

	
	}

	store_idx_vals(src, map_idx_val);

	//string type = get_idx_type(addr);
	//settype(dst, type );

	//printf("\e[32m Variable_store \e[0m src %s content %s result_expr %s\n", src.c_str(), idx_content.c_str(),result_expr.str().c_str());


}

void SolverWrapper::store_idx_vals(string src, map<set<pair<string, int> > , int > map_idx_val){

	if(!check_mangled_name(src)) assert(0 && "Wrong name for store_idx_vals");

	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){

		map<set<pair<string, int> >, int> res;

		set<pair<string, int> > idx_idxvals = it->first;
		int val = it->second;

		set<pair<string, int> > idx_idxval_res;

		for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
			pair<string, int> str_int = (*it2);
			idx_idxval_res.insert(str_int);
		}

		string memname = "mem_" + itos(val);

		map<set<pair<string, int> > , int > mem_idxvals = variables[src].idx_values;
		if(mem_idxvals.size()){
			for( map<set<pair<string, int> > , int >::iterator it3 = mem_idxvals.begin(); it3 != mem_idxvals.end(); it3++ ){
				set<pair<string, int> > mem_idxvals = it3->first;
				int mem_val = it3->second;
				for( set<pair<string, int> >::iterator it4 = mem_idxvals.begin(); it4 != mem_idxvals.end(); it4++ ){
					pair<string, int> str_int = (*it4);
					idx_idxval_res.insert(str_int);
				}

				res[idx_idxval_res] = val;
			}
		} else {
			res[idx_idxval_res] = stoi(realvalue(src));
		}

		variables[memname].idx_values = res;

		debug && printf("\e[32m store_idx_vals \e[0m %s\n", memname.c_str());
		for( map<set<pair<string, int> > , int >::iterator it = res.begin(); it != res.end(); it++ ){
			set<pair<string, int> > idx_idxvals = it->first;
			set<pair<string, int> > idx_idxval_res;

			int val = it->second;

			for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
				pair<string, int> str_int = (*it2);
				string idx = str_int.first;
				int idxval = str_int.second;

				printf("\e[32m idx_values \e[0m %s %d %d\n", idx.c_str(), idxval, val);
			}
		}

	}
	

}

void SolverWrapper::load_idx_vals(string dst, map<set<pair<string, int> > , int > map_idx_val){
	if(!check_mangled_name(dst)) assert(0 && "Wrong name for load_idx_vals");

	map<set<pair<string, int> > , int > res;

	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > idx_idxvals = it->first;
		set<pair<string, int> > idx_idxval_res;

		int val = it->second;


		for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
			pair<string, int> str_int = (*it2);
			//string idx = str_int.first;
			//int idxval = str_int.second;

			idx_idxval_res.insert(str_int);

		}

		set<pair<string, int> > idx_idxval_res_copy = idx_idxval_res;

		string memname = "mem_" + itos(val);
		map<set<pair<string, int> > , int > mem_idxvals = variables[memname].idx_values;
		if(mem_idxvals.size()){
			for( map<set<pair<string, int> > , int >::iterator it3 = mem_idxvals.begin(); it3 != mem_idxvals.end(); it3++ ){
				set<pair<string, int> > mem_idxvals = it3->first;
				idx_idxval_res = idx_idxval_res_copy;
				int mem_val = it3->second;
				for( set<pair<string, int> >::iterator it4 = mem_idxvals.begin(); it4 != mem_idxvals.end(); it4++ ){
					pair<string, int> str_int = (*it4);
					idx_idxval_res.insert(str_int);
				}

				res[idx_idxval_res] = mem_val;
			}
		} else {
			res[idx_idxval_res] = stoi(realvalue(memname));
		}
	}

	variables[dst].idx_values = res;

	debug && printf("\e[32m load_idx_vals \e[0m %s\n", dst.c_str());
	for( map<set<pair<string, int> > , int >::iterator it = res.begin(); it != res.end(); it++ ){
		set<pair<string, int> > idx_idxvals = it->first;
		set<pair<string, int> > idx_idxval_res;

		int val = it->second;

		for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
			pair<string, int> str_int = (*it2);
			string idx = str_int.first;
			int idxval = str_int.second;

			printf("\e[32m idx_values \e[0m %s %d %d\n", idx.c_str(), idxval, val);
		}
	}
}

void SolverWrapper::variable_store(string src, string idx_content, int first_address, int last_address ){

	if(!check_mangled_name(src)) assert(0 && "Wrong name for variable_store");

	string index_expr = idx_content.substr(5);

	string src_content  = content(src);

	for ( unsigned int i = first_address; i <= last_address; i++) {


		string mem_name = "mem_" + itos(i);
		if(get_name_hint(mem_name) == "") continue;

		string prev_content = content(mem_name);

		stringstream result_expr;
		result_expr << "(ite (= " << index_expr << " " << i << ") " << src_content << " " << prev_content << ")";

		setcontent(mem_name, result_expr.str());
		settype(mem_name, get_type(src));
		unset_is_propagated_constant(mem_name);

	}



	printf("\e[32m Variable_store \e[0m src %s content %s first_addr %d last_addr %d \n",src.c_str(),
			idx_content.c_str(), first_address, last_address);



}

