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

#define UNDERSCORE "_"
#define PAUSE_ON_INSERT false
#define EXIT_ON_INSERT false


extern Options* options;
extern Operators* operators;
extern Database* database;
extern Concurrency* concurrency;


Solver::Solver(){

	options->read_options();
	debug = options->cmd_option_bool("verbose");

}
Solver::~Solver(){}


void Solver::free_var(string var){

	if(!check_mangled_name(var)) assert(0 && "Wrong name for content");

	stringstream mem_name; mem_name << "mem_" << variables[var].content;
	forced_free_vars.insert( mem_name.str() );

}

string Solver::content( string name ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	if(name.find("constant_") != string::npos ) return name.substr(9);

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
		return variables[name].content;
	}
}


string Solver::content_2( string name ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	if(name.find("constant_") != string::npos ) return name.substr(9);

	if( variables[name].content == "" || is_forced_free(name) ){
		string position;
	        if(name.substr(0,7) == "global_")
			position = operators->get_actual_function() + UNDERSCORE + variables[name].name_hint;
		else
			position = variables[name].name_hint;
		//insert_variable(name, position );

		if(is_number(name)) return name;
		else return position;
		//return name;

	} else {
		return variables[name].content;
	}
}



void Solver::dump_model(){


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


void Solver::set_last_address(string name, int last_address){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_last_address");

	debug && printf("\e[32m set_last_address %s %d \e[0m\n", name.c_str(), last_address);

	variables[name].last_address = last_address;

}

void Solver::set_first_address(string name, int first_address){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_first_address");

	debug && printf("\e[32m set_first_address %s %d \e[0m\n", name.c_str(), first_address);

	variables[name].first_address = first_address;

}

int Solver::get_last_address(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for get_last_address");
	return variables[name].last_address;

}


int Solver::get_first_address(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for get_first_address");
	return variables[name].first_address;

}

void Solver::dump_pivots(FILE* file){

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
			fprintf(file, "(declare-fun %s () %s)\n", name.c_str(), type.c_str() );
		}
		

	}
	
}

void Solver::clean_pivots(){

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

void Solver::dump_variables(FILE* file){

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = get_type(it->name);

		//dump_variable(position, type, file);
		fprintf(file,"(declare-fun %s () %s)\n", locknames(position).c_str(), type.c_str());

		
	}
	

}

void Solver::dump_conditions(FILE* file){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		fprintf(file,"(assert %s)\n", locknames(it->cond).c_str() );
	}
	
}

string Solver::find_mem_of_id(string id){


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(it->second.name_hint == id){
			return it->first;
		}
	}

	return "";
	
	

}

void Solver::dump_conditions( stringstream& sstr ){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		sstr << it->cond;
	}



}

void Solver::dump_check_sat(FILE* file){


	fprintf(file,"(check-sat)\n");

}

void Solver::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");

}

int Solver::minval(string type){

	if(type == "Int32") return -(1 << 30);
	if(type == "Int16") return -(1 << 15);
	if(type == "Int8")  return -(1 << 7);
	if(type == "Int") return   -(1 << 30);
	if(type == "Pointer") return 0;

	printf("MinVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;
}

int Solver::maxval(string type){

	if(type == "Int32") return (1 << 30);
	if(type == "Int16") return (1 << 15);
	if(type == "Int8") return (1 << 7);
	if(type == "Int") return (1 << 30);
	if(type == "Pointer") return (1 << 30);

	printf("MaxVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;

}

void Solver::dump_type_limits(FILE* file){

	if(options->cmd_option_bool("unconstrained")) return;


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = get_sized_type(it->name);

		string position = it->position;

		if( get_type(it->name) != "Real" )
			fprintf(file,"(assert (and (>= %s %d) (< %s %d)))\n", position.c_str(), minval(type), position.c_str(), maxval(type) );
		
	}
}

void Solver::dump_tail(FILE* file){

	fprintf(file,"(exit)\n");
}

bool Solver::need_for_dump(string name, string content){
		if( content == "" ) return false;
		if( name.find("_pivot_") != string::npos ) return false;
		if( gettype(name) == "Function") return false;
		if( get_is_propagated_constant(name) ) return false;
		return true;
}

void Solver::dump_get(FILE* file){



	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n", locknames(it->position).c_str(), it->name.c_str() );
	}
	
	fprintf(file,"; --- ↑free ↓non-free \n" );

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;
		
		//printf("----- name %s type %s\n", it->first.c_str(), gettype(it->first).c_str() );

		fprintf(file,"(get-value (%s)); %s\n", locknames(it->second.content).c_str(), it->first.c_str() );
	}

	fprintf(file,"; --- ↑non-free ↓forced_free \n" );

	//for( set<string>::iterator it = forced_free_vars.begin(); it != forced_free_vars.end(); it++ ){
		//fprintf(file,"(get-value (%s));\n", get_first_content(*it).c_str() );
	//}
	
	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		fprintf(file, "(get-value (%s)); %s\n", it->second.c_str(), it->first.c_str());
	}
	
	
	
}

int Solver::get_num_fvars(){


	return free_variables.size();

}

string Solver::result_get(string get_str){


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

void Solver::set_real_value(string varname, string value){


	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	//printf("set_real_value %s %s\n", varname.c_str(), value.c_str());
	variables[varname].real_value = value;
}

void Solver::set_real_value_mangled(string varname, string value ){


	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[varname].real_value = value;
}

void Solver::set_real_value_hint(string hint, string value ){



	printf("set_real_value_hint %s %s\n", hint.c_str(), value.c_str());

	
	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(it->second.name_hint == hint){
			it->second.real_value = value;
			return;

		}
			
	}

	assert(0 && "Variable not found");
	
}



#define INITIAL_LINE_LENGTH	256
char* fgetln(register FILE* fp, size_t *lenp) {

	char c;
	size_t n, siz;
	size_t len, new_len;
	char *buf;
	char *p;

	len = INITIAL_LINE_LENGTH;
	n = siz = 0;

	if ((buf = (char*)malloc(INITIAL_LINE_LENGTH + 1)) == NULL)
		return (NULL);

	p = buf;
	for (;;) {
		if ((c = getc(fp)) == EOF) {
			if (siz != 0)
				break;
			free(buf);
			return (NULL);
		}

		++siz;

		if (c == '\n') {
			*p++ = c;
			break;
		}
		if (n++ >= len) {
			new_len = len << 1;
			if ((buf = (char*)realloc(buf, new_len + 1)) == NULL)
	                        return (NULL);
			len = new_len;
			p = buf;
	                p += len >> 1;
		}
		*p++ = c;
	}
	*p = 0;
	if (lenp != NULL)
		*lenp = siz;
	return (buf);
}

bool Solver::get_is_sat(string is_sat){

	if( is_sat == "sat" ) return true;
	else return false;
}

bool sat;

void Solver::solve_problem(){

	if(options->cmd_option_str("max_depth") != "" && conditions.size()-1 > options->cmd_option_int("max_depth")){
		sat = 0;
		return;
	}

	vector<string> ret_vector;

	sat = 0;

	stringstream filename;
	filename << "z3_" << rand() << ".smt2";


	FILE* file = fopen(filename.str().c_str(), "w");


	options->read_options();

	dump_header(file);
	dump_variables(file);
	dump_pivots(file);
	//concurrency->dump_remaining_variables(free_variables, file);
	dump_type_limits(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_get(file);
	dump_tail(file);

	fclose(file);

	debug && printf("\e[31m filename solve problem \e[0m %s\n", filename.str().c_str() );

	if(options->cmd_option_bool("see_each_problem"))
		getchar();



	FILE *fp;
	stringstream command;

	command << "z3 " << filename.str();
	command << " > /tmp/z3_output";
	system(command.str().c_str());

	ifstream input("/tmp/z3_output");
	string line;
	
	while( getline( input, line ) ) {
		ret_vector.push_back(line);
	}
	
	string         sat_str       = ret_vector[0];

	if(sat_str.find("error") != string::npos )
		assert(0 && "Error in z3 execution");
	if(sat_str.find("unknown") != string::npos )
		printf("Warning: unknown sat\n");

	sat = get_is_sat(sat_str);

	debug && printf("\e[31m problem solved \e[0m\n" );

	if(!sat) return;


	bool sat = 0;


	vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	set<NameAndPosition> free_variables_aux;

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++,it_ret++ ){

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string varname = it->name;
		string value = result_get(*it_ret);
		string hint = it->position;


		debug && printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);

		NameAndPosition nandp = {varname, hint, value};
		free_variables_aux.insert(nandp);
		//it->value = value;
		//set_real_value_hint(hint, value);
		//variables[varname].real_value = value;

	}

	free_variables = free_variables_aux;


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string name = it->first;
		string value = result_get(*it_ret);


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);
		//variables[name].real_value = value;

		it_ret++;
	}


	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		set_first_content_value(it->first, result_get(*it_ret));

		it_ret++;
	}

}

bool Solver::solvable_problem(){


	return sat;
	
}

void Solver::set_sat(bool _sat){

	sat = _sat;
}

void Solver::insert_variable(string name, string position){



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
		
	debug && printf("\e[35m Insert_variable \e[0m name %s hint %s position %s\n", name.c_str(), variables[name].name_hint.c_str(), position.c_str() );

	if( PAUSE_ON_INSERT )
		getchar();

	if( EXIT_ON_INSERT )
		exit(0);

	NameAndPosition nandp = {name, position};
	free_variables.insert(nandp);

}

void Solver::insert_variable_2(string name, string position){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for insert_variable");
		
	debug && printf("\e[35m Insert_variable \e[0m name %s hint %s position %s\n", name.c_str(), variables[name].name_hint.c_str(), position.c_str() );


	NameAndPosition nandp = {name, position};
	free_variables.insert(nandp);

}

void Solver::push_condition(string cond, bool invert ){

	set<string> joints_set;
	string fn = "";
	Condition condition = { invert?negation(cond):cond, fn, joints_set };

	conditions.push_back( condition );

}



void Solver::push_condition_static(string cond, bool invert){


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




vector<bool> path_stack_save;
vector<string> conditions_static_save;
vector<Condition> conditions_save;


void Solver::save_state(){
	path_stack_save        = path_stack;
	conditions_static_save = conditions_static;
	conditions_save        = conditions;
}

void Solver::load_state(){
	path_stack        = path_stack_save;
	conditions_static = conditions_static_save;
	conditions        = conditions_save;
}

void Solver::push_condition(string name, string actual_function, vector<string> joints, bool invert){

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

void Solver::push_condition(string cond, string fn, vector<string> joints ){

	//printf("condition comes_from_non_annotated %d\n", get_comes_from_non_annotated(cond) );


	set<string> joints_set = set<string>(joints.begin(), joints.end());

	Condition condition = { cond, fn, joints_set };
	conditions.push_back( condition );
}

string Solver::negation(string condition){


	stringstream negation_ss;
	negation_ss << "(not " << string(condition) << ")";

	return negation_ss.str();
}

string Solver::negateop(string predicate){

	if( predicate == "="  ) return "#";
	if( predicate == ">"  ) return "<=";
	if( predicate == ">=" ) return "<";
	if( predicate == "<"  ) return ">=";
	if( predicate == "<=" ) return ">";
	if( predicate == "#"  ) return "=";
	assert(0 && "Unknown Operation");

}

string Solver::name_without_suffix( string name ){


	if(!check_mangled_name(name)) assert(0 && "Wrong name for name_without_suffix");

	int s1 = name.find(UNDERSCORE);
	int s2 = name.find(UNDERSCORE, s1+1);
	return name.substr(0,s2);
}

string Solver::get_sized_type(string name){


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

	if (variables[name].type == "Int")
		return "Int";

	if (variables[name].type == "PointerTyID")
		return "Pointer";


	printf("name %s type %s\n", name.c_str(), variables[name].type.c_str() );

	assert(0 && "Unknown Type");

	return "Int";

}

void Solver::set_comes_from_non_annotated(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for set_comes_from_non_annotated");

	debug && printf("\e[32m set_comes_from_non_annotated \e[0m %s \n", name.c_str() );

	variables[name].comes_from_non_annotated = true;
	
	
}

bool Solver::get_comes_from_non_annotated(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for get_comes_from_non_annotated");

	return variables[name].comes_from_non_annotated;
	
	
}

void Solver::clean_conditions_stack(string name){

//typedef struct Condition {
	//string cond;
	//string function;
	//set<string> joints;
//} Condition;
	
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

string Solver::realvalue_mangled(string varname){


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

string Solver::realvalue(string varname){


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

void Solver::set_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for set_is_propagated_constant");

	variables[varname].is_propagated_constant = true;

}


void Solver::unset_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for unset_is_propagated_constant");

	variables[varname].is_propagated_constant = false;

}

bool Solver::is_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for is_constant");

	return varname.substr(0,9) == "constant" UNDERSCORE;

}

void Solver::setcontent(string varname, string content){


	debug && printf("\e[31m setcontent %s %s\e[0m.\n", varname.c_str(), content.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for setcontent");
	variables[varname].content = content;
}

bool Solver::is_forced_free(string position){

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

}


bool Solver::is_forced_free_2(string position){

	if(!check_mangled_name(position)) assert(0 && "Wrong src for is_forced_free");

	if( forced_free_vars.find(position) != forced_free_vars.end() ){
		return true;
	} else {
		return false;
	}

}


void Solver::load_forced_free_vars(){


	ifstream input("free_vars");
	string line;
	
	while( getline( input, line ) ) {
		forced_free_vars.insert(line);
	}
	
}

//void Solver::substitute_pivots(string& src){

	//for( map<string,vector<string> >::iterator it = pivot_variables.begin(); it != pivot_variables.end(); it++ ){
		////printf("subst_pivot %s\n", it->first.c_str() );
		////if( get_name_hint(src) == it->first ){
		//if( src == it->first ){
			//vector<string> pivots = it->second;
			//string subst_to = pivots[pivots.size()-1];
			//printf("\n\e[33m Substitute_pivot_point\e[0m %s %s\n", it->first.c_str(), subst_to.c_str());
			//src = subst_to;
			////set_name_hint(src, subst_to);
		//}
	//}

//}

//bool Solver::is_pivot(string src){
	////string content_var = variables[src].content;
	////if(content_var.find("_pivot_") == string::npos)
	//if(src.find("_pivot_") == string::npos)
		//return false;
	//else
		//return true;
	////printf("is_pivot %s\n", content(src).c_str());
//}

void Solver::set_first_content(string src, string content){

	printf("\e[36m set_first_content %s %s\e[0m\n", src.c_str(), content.c_str());

	first_content[src] = content;

}

void Solver::set_first_content_value(string var, string value){
	printf("\e[36m set_first_content_value %s %s\e[0m\n", var.c_str(), value.c_str() );
	first_content_value[var] = value;
}

string Solver::get_first_content_value(string var){
	return first_content_value[var];
}

string Solver::get_first_content(string src){

	return first_content[src];

}


void Solver::propagate_unary(string src, string dst, bool forcedfree){

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

}



void Solver::assign_instruction(string src, string dst, string fn_name){

	//substitute_pivots(src);
	
	debug && printf("\n\e[32m Assign_instruction %s = %s \e[0m\n",dst.c_str(),src.c_str() );

	if(!check_mangled_name(src)) assert(0 && "Wrong src for assign");
	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for assign");



	//if( !is_pivot(src) ){
		//printf("not pivot\n");
		
		bool forcedfree = is_forced_free(src);
		if(forcedfree){

			string cntnt = variables[src].content;
			debug && printf("\e[36m Source is forced_free %s %s\e[0m\n",src.c_str(), cntnt.c_str());
			setcontent(src, "");
		}
		variables[dst].content = content(src);

		if(forcedfree){
			set_first_content(src, variables[dst].content);
			printf("variables[dst].content %s\n", variables[dst].content.c_str() );

		}

	//} else {
		//printf("pivot\n");
		//variables[dst].content = variables[src].content;
	//}

	propagate_unary(src, dst, forcedfree);

	//if( variables[dst].type == "" ) assert(0 && "No type in dst");
	string prev_type = variables[dst].type;
	string new_type = get_type(src);

	settype(dst, get_type(src));

	if(is_constant(src) && prev_type != new_type && prev_type != "Pointer" && prev_type != ""){
		printf("Types %s %s\n", prev_type.c_str(), new_type.c_str());
		settype(dst, prev_type);
	}

	//printf("set_real_value inside assign %s %s %s\n", dst.c_str(), src.c_str(), realvalue(src).c_str() );
	set_real_value( dst, realvalue(src) );



	//debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s\n", variables[dst].content.c_str(), variables[dst].type.c_str() );
	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s %s %s\e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d %d \e[32m lastaddress\e[0m  %d %d \e[32m \e[32m firstaddress \e[0m \e[0m %d %d\n",
                 variables[dst].content.c_str(),
		 variables[src].type.c_str(), variables[dst].type.c_str(), prev_type.c_str(),
		 realvalue(dst).c_str(), get_is_propagated_constant(src), get_is_propagated_constant(dst),
		 get_last_address(src), get_last_address(dst), get_first_address(src), get_first_address(dst) );



}

bool Solver::implemented_operation(string operation){

	if(operation == "<=") return true;
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

void Solver::propagate_binary(string op1, string op2, string dst){

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

}

string binary_rep(int n){

	stringstream ret;

	for( int c = 30; c >= 0; c--){
		int k = n >> c;
		if(k & 1)
			ret << 1;
		else 
			ret << 0;
	}

	return ret.str();
}

//string Solver::and_constant(string op1, string op2){

	//stringstream ret;
	//int op2_i = stoi(op2);
	//string op2_b = binary_rep(op2_i);
	//string op1_content = content(op1);

	//printf("and_constant %s %s %s %s\n", op1.c_str(),op1_content.c_str(), op2.c_str(), op2_b.c_str());

	//ret << "(+ ";

	//for ( unsigned int i = 0,mult=1,mult2=2; i < op2_b.length()-1; i++,mult*=2, mult2*=2) {
		//char byte = op2_b[op2_b.length()-i-1];
		//printf("byte %c mult %d\n", byte, mult);

		//stringstream bit;

		//bit << "(/ (- (mod " << op1_content << " " << mult2 << ") (mod " << op1_content << " " << mult << ")) " << mult <<  ")";

		//if( byte == '1' )
			//ret << "(* " << bit.str() << " " << mult << ") ";

	//}

	//ret << ")";

	//return ret.str();

//}

string Solver::and_constant(string op1, string op2){

	stringstream ret;
	int op2_i = stoi(op2);
	string op2_b = binary_rep(op2_i);
	string content1 = content(op1);

	printf("and_constant %s %s %s %s\n", op1.c_str(),content1.c_str(), op2.c_str(), op2_b.c_str());


	vector<string> z_bits;

	for ( unsigned int i = 0,mult1=1,mult2=2; i < op2_b.length()-1; i++,mult1*=2, mult2*=2) {

		char bit = op2_b[op2_b.length()-i-1];

		printf("bit %c mult %d\n", bit, mult1);

		stringstream x_bit_i_sh;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i_sh << "(- (mod " << content1 << " " << mult2 << ") (mod " << content1 << " " << mult1 << "))";

		if(bit == '1'){
			z_bit_i_sh << x_bit_i_sh.str();
		} else {
			z_bit_i_sh << "";
		}


		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < z_bits.size(); i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;



	return ret.str();

}


string Solver::complement_op(string op1){

	stringstream ret;
	string content1 = content(op1);

	printf("complement_operation %s \n", op1.c_str());

	//ret << "(ite (> " << content1 << " 0) (- (+ " << content1 << " 1)) (- -256 (+ " << content1 << " 1)))";
	//ret << "(ite (> " << content1 << " 0) (- (+ " << content1 << " 1)) (- -256 (+ " << content1 << " 2)))";
	ret << "(- (+ " << content1 << " 1))";

	return ret.str();

}

string Solver::or_constant(string op1, string op2){

	stringstream ret;
	int op2_i = stoi(op2);
	string op2_b = binary_rep(op2_i);
	string content1 = content(op1);

	printf("or_constant %s %s %s %s\n", op1.c_str(),content1.c_str(), op2.c_str(), op2_b.c_str());


	vector<string> z_bits;

	for ( unsigned int i = 0,mult1=1,mult2=2; i < op2_b.length()-1; i++,mult1*=2, mult2*=2) {

		char bit = op2_b[op2_b.length()-i-1];

		printf("bit %c mult %d\n", bit, mult1);

		stringstream x_bit_i_sh;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i_sh << "(- (mod " << content1 << " " << mult2 << ") (mod " << content1 << " " << mult1 << "))";

		if(bit == '1'){
			z_bit_i_sh << "(- " << mult1 << " " << x_bit_i_sh.str() << ")";
		} else {
			z_bit_i_sh << "";
		}


		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < z_bits.size(); i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + content1 + " " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;



	return ret.str();

}

//string wired_and( string op1, string op2, int nbits ){

	//vector<string> z_bits;

	//for ( unsigned int i = 0; i < nbits; i++) {
		//int mod1 = ( 1 << i+1 );
		//int mod2 = ( 1 << i   );

		//string content1 = content(name(op1));
		//string content2 = content(name(op2));
		
		////printf("content %s %s\n", content1.c_str(), content2.c_str() );

		//stringstream x_bit_i;
		//stringstream y_bit_i;
		//stringstream z_bit_i;
		//stringstream z_bit_i_sh;
		//x_bit_i << "(/ (- (mod " << content1 << " " << mod1 << ") (mod " << content1 << " " << mod2 << ")) " << mod2 << ")";
		//y_bit_i << "(/ (- (mod " << content2 << " " << mod1 << ") (mod " << content2 << " " << mod2 << ")) " << mod2 << ")";

		//z_bit_i << "(* " << x_bit_i.str() << " " << y_bit_i.str() << ")";

		//z_bit_i_sh << "(* " << z_bit_i.str() << " " << mod2 << ")";

		//z_bits.push_back(z_bit_i_sh.str());
	//}

	//string res;

	//for ( unsigned int i = 0; i < nbits; i++) {
		//res += z_bits[i] + " ";
	//}

	//res = "(+ " + res + ")";

	////printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	//return res;

//}






void Solver::binary_instruction(string dst, string op1, string op2, string operation){

	//substitute_pivots(op1);
	//substitute_pivots(op2);

	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for binary_instruction");
	if(!check_mangled_name(op1)) assert(0 && "Wrong op1 for binary_instruction");
	if(!check_mangled_name(op2)) assert(0 && "Wrong op2 for binary_instruction");
	if(!implemented_operation(operation)) assert(0 && "Not implemented operation");

	debug && printf("\n\e[32m Binary_instruction %s = %s %s %s (%s %s)\e[0m\n",
			dst.c_str(),op1.c_str(), operation.c_str(),op2.c_str(),
		        get_type(op1).c_str(), get_type(op2).c_str() );


	stringstream content_ss;


	if( operation == "#" ){
		content_ss << "(not (= " << content(op1 ) << " " <<  content(op2 ) << "))";
	} else if (operation == "%") {
		content_ss << "(mod " << content(op1 ) << " " <<  content(op2 ) << ")";
	} else if (operation == "R" ) {

		//if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		if(!is_constant(op2)) assert(0 && "Rotate non-constant");
		int exponent = stoi( op2.substr(9) );
		int factor = 1 << exponent;

		content_ss << "(/ " << content(op1) << " " << factor << ")";

	} else if (operation == "L" ) {

		//if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		if(!is_constant(op2)) assert(0 && "Rotate non-constant");
		int exponent = stoi( op2.substr(9) );
		int factor = 1 << exponent;

		content_ss << "(* " << content(op1) << " " << factor << ")";

	} else if (operation == "Y" ) {

		if( is_constant(op2) )
			content_ss << and_constant( op1, realvalue(op2) );
		else
			assert(0 && "Non-Supported Operation");
	} else if (operation == "O" ) {

		if( is_constant(op2) )
			content_ss << or_constant( op1, realvalue(op2) );
		else
			assert(0 && "Non-Supported Operation");
	} else if (operation == "X" ) {
		if( is_constant(op2) && realvalue(op2) == "-1" )
			content_ss  << complement_op( op1 );
		else
			assert(0 && "Non-Supported Operation");
	} else {
		content_ss << "(" << operation << " " << content(op1 ) << " " <<  content(op2 ) << ")";
	}

	//debug && printf("\e[31m type \e[0m %s \e[31m op2 \e[0m %s \e[31m operation \e[0m %s\n", variables[op1].type.c_str(), op2.c_str(), operation.c_str() );
	

	variables[dst].content = content_ss.str();

	if( variables[op1].type != "" )
		settype(dst, get_type(op1));
	else
		settype(dst, get_type(op2));


	propagate_binary(op1, op2, dst);

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
		//fflush(stdout); fflush(stderr);
		//printf("realvalue_op1 %s realvalue_op2 %s\n", realvalue(op1).c_str(), realvalue(op2).c_str() );

		string value_1_s = realvalue(op1);
		string value_2_s = realvalue(op2);
		int value_1;
		int value_2;

		if(value_1_s == "true"){
			value_1 = 1;
		} else if(value_1_s == "false"){
			value_1 = 0;
		} else {
			value_1 = stoi(value_1_s);
		}

		if(value_2_s == "true"){
			value_2 = 1;
		} else if(value_2_s == "false"){
			value_2 = 0;
		} else {
			value_2 = stoi(value_2_s);
		}

		set_real_value(dst, ( value_1 != value_2 )?"true":"false" );
	}


	if(operation == "+"){

		stringstream result;
		if( get_type(dst) == "Real" ){
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else if (get_type(dst) == "Int") {
			result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		} else if( get_type(dst) == "Pointer" ) {
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else {
			assert(0 && "Unknown type");
		}

		set_real_value(dst, result.str());
	}

	if(operation == "-"){


		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) - stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	}

	if(operation == "*"){

		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) * stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) * stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	}


	if(operation == "/"){


		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) / stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) / stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");

		set_real_value(dst, result.str());
	}


	if(operation == "%"){
		stringstream result; result << stoi(realvalue(op1)) % stoi(realvalue(op2));
		set_real_value(dst, result.str());
	}

	if(operation == "R"){
		//if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		if(!is_constant(op2)) assert(0 && "Rotate non-constant");
		int places = stoi( op2 );

		int result_i = stoi(realvalue(op1)) >> places;

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

		//printf("rotate %s %s\n", realvalue(op1).c_str(), result.str().c_str());

	}

	if( operation == "Y" ){
		int op1_i = stoi(realvalue(op1));
		int op2_i = stoi(realvalue(op2));
		int res = op1_i & op2_i;
		stringstream result; result << res;
		set_real_value(dst, result.str());
	}

	if( operation == "O" ){
		int op1_i = stoi(realvalue(op1));
		int op2_i = stoi(realvalue(op2));
		int res = op1_i | op2_i;
		stringstream result; result << res;
		set_real_value(dst, result.str());
	}

	if( operation == "X" ){
		if( is_constant(op2) && realvalue(op2) == "-1" ){
			int op1_i = stoi(realvalue(op1));
			int res = ~op1_i;
			stringstream result; result << res;
			set_real_value(dst, result.str());
		}
	}

	if( variables[op1].type != "" ) variables[dst].type = variables[op1].type;
	if( variables[op2].type != "" ) variables[dst].type = variables[op2].type;


	if( variables[op1].type == "bool" && op2 == "constant_0" && operation == "#" ){
		debug && printf("\e[32m Propagation of bool constraint \e[0m\n");

		content_ss.str("");
		content_ss << content(op1);
		variables[dst].content = content_ss.str();

		set_real_value(dst, realvalue(op1) );
	}



	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d \e[32m last_address\e[0m  %d %d \e[32m firstaddress \e[0m %d %d\n",
                 variables[dst ].content.c_str(), variables[dst].type.c_str(), realvalue(dst).c_str(),
		get_is_propagated_constant(dst),
		get_last_address(op1), get_last_address(dst), get_first_address(op1), get_first_address(dst) );


}

int Solver::show_problem(){


	options->read_options();
	
	if(!options->cmd_option_bool("show_only_constraints")){
	dump_header();
	dump_variables();
	dump_pivots();
	//concurrency->dump_remaining_variables(free_variables, file);
	dump_type_limits();}
	dump_conditions();
	if(!options->cmd_option_bool("show_only_constraints")){
	dump_check_sat();
	dump_get();
	dump_tail();}






	stringstream filename; filename << "z3-" << rand() << ".smt2";

	debug && printf("\e[31m filename \e[0m %s\n", filename.str().c_str() );

	FILE* file = fopen(filename.str().c_str(), "w");

	dump_header(file);
	dump_variables(file);
	dump_pivots(file);
	//concurrency->dump_remaining_variables(free_variables, file);
	dump_type_limits(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_tail(file);

	fclose(file);



	fflush(stdout);

	getchar();
}

string Solver::get_offset_tree( string varname ){

	//assert(check_mangled_name(varname) && "Incorrect name for get_offset_tree");
	//printf("get_offset_tree %s %s\n", varname.c_str(), variables[varname].tree.c_str() );
	return variables[varname].tree;
}

bool Solver::check_mangled_name(string name){

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

bool Solver::get_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for get_is_propagated_constant");
	if(is_forced_free_2(varname)) return false;
	return variables[varname].is_propagated_constant;
}

string Solver::gettype(string name){

	//printf("gettype %s\n", name.c_str());

	if( variables.find(name) == variables.end() ) assert(0 && "Not such variable");

	if(name.find("_pivot_") != string::npos)
		name = name.substr(0, name.find("_pivot_"));

	return variables[name].type;
}

void Solver::set_name_hint(string name, string hint){

	debug && printf("\e[35m set_name_hint \e[0m name %s hint %s \n", name.c_str(), hint.c_str() );

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_name_hint");

	variables[name].name_hint = hint;
}

string Solver::get_name_hint(string name){

	//debug && printf("\e[33m get_name_hint %s %s\e[0m\n", name.c_str(), variables[name].name_hint.c_str() );

	return variables[name].name_hint;
}

string Solver::find_by_name_hint(string hint){

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

void Solver::set_offset_tree( string varname, string tree ){

	//assert(check_mangled_name(varname) && "Incorrect name for set_offset_tree");
	//printf("set_offset_tree %s %s\n", varname.c_str(), tree.c_str() );
	variables[varname].tree = tree;
}

void Solver::settype(string name, string type){

	// debug && printf("\e[32m Settype \e[0m. %s %s\n", name.c_str(), type.c_str() );

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for settype");
	variables[name].type = type;

}

string Solver::get_type(string name){

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

vector<bool> Solver::get_path_stack(){

	return path_stack;
}

string Solver::get_path_stack_str(){

	string ret;
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		if(*it)
			ret += "T";
		else
			ret += "F";
	}
	
	return ret;
}

void Solver::push_path_stack(bool step){

	path_stack.push_back(step);
}




void Solver::print_path_stack(){



	printf("\e[33m Path_stack \e[0m");
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		printf("%s", (*it)?"T":"F" );
	}
	printf("\n");

	printf("\e[33m Depth \e[0m %lu\n", path_stack.size());
	

}

map<string, Variable> Solver::get_map_variables(){

	return variables;
}

string Solver::get_anded_stack_conditions(){

	stringstream ret;

	ret << "(and ";
	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		string condition = it->cond;
		ret << condition << " ";
	}

	ret << ")";

	return ret.str();
	

}


string Solver::get_comma_stack_conditions(){

	stringstream ret;

	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		string condition = it->cond;
		ret << condition << ",";
	}


	return ret.str();
	

}

string Solver::get_comma_stack_conditions_static(){

	stringstream ret;

	for( vector<string>::iterator it = conditions_static.begin(); it != conditions_static.end(); it++ ){
		string condition = *it;
		ret << condition << ",";
	}


	return ret.str();

}

vector<Condition> Solver::get_stack_conditions(){

	return conditions;
}

set<NameAndPosition> Solver::get_free_variables(){
	return free_variables;
}

string Solver::get_position(string name){


	return variables[name].name_hint;

}

void Solver::pivot_variable(string variable, string name){


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


vector<int> jump_offsets(string offset_tree){

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

void Solver::pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base){

	vector<int> jmp_offsets = jump_offsets(offset_tree);

	assert( jmp_offsets.size() == indexes.size() );

	string expr = "idx: (+ " + content(base) + " ";
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		stringstream subexpr;
		subexpr << "(* " << content(indexes[i]) << " " << jmp_offsets[i] << ") ";
		expr += subexpr.str();
	}

	expr += ")";

	setcontent(dst, expr);

	bool forcedfree = is_forced_free(base);
	propagate_unary(base, dst, forcedfree);

	debug && printf("\e[32m pointer_instruction \e[0m last_addr %d first_addr %d last_addr %d first_addr %d\n",
			get_last_address(base), get_first_address(base),
			get_last_address(dst) , get_first_address(dst)
			);

}


void Solver::variable_load(string dst, string idx_content, int first_address, int last_address ){

	if(!check_mangled_name(dst)) assert(0 && "Wrong name for variable_load");

	string index_expr = idx_content.substr(5);
	stringstream result_expr;

	int m = 0;
	for ( unsigned int i = first_address; i <= last_address; i++) {
		string mem_name = "mem_" + itos(i);
		if(get_name_hint(mem_name) == "") continue;
		result_expr << "(ite (= " << index_expr << " " << i << ") " << content(mem_name) << " ";
		m++;
	}

	result_expr << "0";

	for ( unsigned int i = 0; i < m; i++) {
		result_expr << ")";
	}

	setcontent(dst, result_expr.str());

	settype(dst, get_type("mem_" + itos(first_address)));

	printf("\e[32m Variable_load \e[0m dst %s content %s first_addr %d last_addr %d result_expr %s\n", dst.c_str(), idx_content.c_str(), first_address, last_address, result_expr.str().c_str());


}



void Solver::variable_store(string src, string idx_content, int first_address, int last_address ){

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

