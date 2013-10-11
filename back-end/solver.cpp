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
#define PAUSE_ON_INSERT false
#define EXIT_ON_INSERT false
#define FUZZ_LIMIT 500

map<string, Variable> variables;
set<NameAndPosition> variable_names;
vector<string> flatened_conditions;
set<string> flatened_variables;
extern string actual_function;
vector<Condition> conditions;
vector<bool> path_stack;
vector<string> exclusions;

void push_path_stack(bool step){
	path_stack.push_back(step);
}

set<string> forced_free_vars;

void free_var(string var){

	//printf("free_var %s prev_value %s\n", var.c_str(), variables[name(var)].content.c_str() );
	stringstream mem_name; mem_name << "mem_" << variables[name(var)].content;
	forced_free_vars.insert( mem_name.str() );

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
		   tokens[0].substr(0,3) != "mem"      &&
		   tokens[0].substr(0,6) != "global"
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

void dump_sync_variables(FILE* file){

	set<pair<string, string> > vars_and_types = get_sync_global_types();

	for( set<pair<string, string> >::iterator it = vars_and_types.begin(); it != vars_and_types.end(); it++ ){
		stringstream decl; decl << "(declare-fun " << it->first << " () " << it->second << ")";

		bool found = false;

		for( set<NameAndPosition>::iterator it2 = variable_names.begin(); it2 != variable_names.end(); it2++ ){

			vector<string> tokens = tokenize(it2->name, " ");

			string name = tokens[0];

			if(name == it->first)
				found = true;
		}
		

		if(!found)
			fprintf(file, "%s\n", decl.str().c_str() );
	}
	
}

void dump_conditions(FILE* file){

	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if(!it->fuzzme)
			fprintf(file,"(assert %s)\n", it->cond.c_str() );
	}
	
}

set<string> sync_points_and_locks;

void solver_insert_sync_point(string lockunlock, string sync_name, string mutex_name){
	sync_points_and_locks.insert( "(" + lockunlock + "_" + mutex_name + ")" );
}


map<string, set<string> > concurrency_table;

set<string> unlock_points(string mutex){

	//printf("listing_unlock %s\n", mutex.c_str());
	set<string> ret = concurrency_table[mutex];
	//for( set<string>::iterator it = ret.begin(); it != ret.end(); it++ )
		//printf("%s \n", it->c_str());
	//printf("\n");
	if(!ret.size()){
		//printf("mutex %s\n", mutex.c_str() ); fflush(stdout);
		assert(0 && "empty set");
	}
	return ret;
	//set<string> set_a; set_a.insert("d");
	//set<string> set_b; set_b.insert("e"); set_b.insert("f");
	//if(mutex == "a")
		//return set_a;
	//if(mutex == "b")
		//return set_b;
	//return set_a;

}

string or_unlocking(string condition, string mutex){

	stringstream ret;
	set<string> unlocks = unlock_points(mutex);

	if(unlocks.size() > 1)
		ret << "(or ";


	for( set<string>::iterator it = unlocks.begin(); it != unlocks.end(); it++ ){
		ret << "(" << "unlock_" << (*it) << ") ";
	}

	if(unlocks.size() > 1)
		ret << ")";

	return ret.str();


}

void substitute_locks(string& condition){

	set<string> mutexes = list_semaphores();
	//mutexes.insert("a");
	//mutexes.insert("b");
	//mutexes.insert("c");

	for( set<string>::iterator it = mutexes.begin(); it != mutexes.end(); it++ ){
		string expr_find = string("(lock_") + (*it) + string(")");
		string expr_subs = or_unlocking(condition, *it);
		myReplace(condition, expr_find, expr_subs);
	}
	
	

}

string or_paths(string dest){

	//printf("or_paths %s\n", dest.c_str());

	//if(dest == "bb")    return "(de)";
	//if(dest == "bb1")   return "(df)";
	//if(dest == "bb2")   return "(deg o dfg)";
	//if(dest == "bb4")   return "(bb4)";
	//if(dest == "entry") return "(1)";
	//return "()";

	set<vector<string> > paths = get_paths_to(dest);

	//printf("dest %s path num %lu\n",dest.c_str(), paths.size());

	stringstream ret;
	if(paths.size() > 1)
		ret << "(or ";
	for( set<vector<string> >::iterator it = paths.begin(); it != paths.end(); it++ ){
		vector<string> path = (*it);
		if(path.size() > 1)
			ret << "(and ";
		for( vector<string>::iterator it2 = path.begin(); it2 != path.end(); it2++ ){
			ret << "(statepath_" << (*it2) << ")" << " ";
		}
		if(path.size() > 1)
			ret << ") ";
	}
	if(paths.size() > 1)
		ret << ")";

	//return "(" + dest + ")";
	return ret.str();
	
}

void substitute_unlocks(string& condition){

	//printf("substitute_unlocks\n");

	set<string> unlock_points = list_unlock_points();

	//printf("unlock_points.size %lu\n", unlock_points.size());
	
	for( set<string>::iterator it = unlock_points.begin(); it != unlock_points.end(); it++ ){
		//printf("unlock_point %s\n", it->c_str());
		string expr_find = string("(unlock_") + (*it) + string(")");
		string expr_subs = or_paths(*it);
		myReplace(condition, expr_find, expr_subs);
	}
	

}

void substitute_paths(string& condition){

	//printf("substitute_unlocks\n");

	set<string> unlock_points = list_unlock_points();

	//printf("unlock_points.size %lu\n", unlock_points.size());
	
	for( set<string>::iterator it = unlock_points.begin(); it != unlock_points.end(); it++ ){
		//printf("unlock_point %s\n", it->c_str());
		string expr_find = string("(statepath_") + (*it) + string(")");
		string expr_subs = "(and (stores_" + (*it) + ") (conds_" + (*it) + "))";
		myReplace(condition, expr_find, expr_subs);
	}

}

map<string, set<pair<string, string> > > stores;

string and_stores(string sync_point){

	load_stores(stores);
	//stores["entry"].insert(pair<string, string>("mem_220","mem_216"));
	//stores["bb"].insert(pair<string, string>("mem_119","1"));
	//stores["bb1"].insert(pair<string, string>("mem_119","0"));

	//printf("and_stores %s\n", sync_point.c_str());

	set<pair<string, string> > stores_of_sync_point = stores[sync_point];
	
	stringstream ret;

	if(stores_of_sync_point.size() > 1)
		ret << "(and ";
	for( set<pair<string, string> >::iterator it = stores_of_sync_point.begin(); it != stores_of_sync_point.end(); it++ ){
		ret << "(= " << it->first << " " << it->second << ")";
	}
	if(stores_of_sync_point.size() > 1)
		ret << ")";
	

	return ret.str();


	//if(sync_point == "entry")  return "(= mem_220 mem_216)";
	//if(sync_point == "bb")     return "(= mem_119 1)";
	//if(sync_point == "bb1")    return "(= mem_119 0)";
	//return "()";



}


void substitute_stores(string& condition){

	//printf("substitute_stores\n");

	set<string> sync_points = list_store_sync_points();

	//printf("sync_points.size %lu\n", sync_points.size());
	
	for( set<string>::iterator it = sync_points.begin(); it != sync_points.end(); it++ ){
		//printf("sync_store_point %s\n", it->c_str());
		string expr_find = string("(stores_") + (*it) + string(")");
		string expr_subs = and_stores(*it);
		myReplace(condition, expr_find, expr_subs);
	}
}

map<string, string> stacks;

string stack(string sync_point){

	load_stacks(stacks);
	return stacks[sync_point];

	//if(sync_point == "entry") return "(true)";
	//if(sync_point == "bb")    return "(= mem_123 25)";
	//if(sync_point == "bb4")   return "(not (= mem_123 25))";
	//if(sync_point == "bb2")   return "(true)";
	//if(sync_point == "bb1")   return "(not (= mem_123 12))";
	//return "";
	
}

void substitute_conds(string& condition){

	//printf("substitute_conds\n");

	set<string> sync_points = list_sync_points();

	//printf("sync_points.size %lu\n", sync_points.size());
	
	for( set<string>::iterator it = sync_points.begin(); it != sync_points.end(); it++ ){
		//printf("sync_point %s\n", it->c_str());
		string expr_find = string("(conds_") + (*it) + string(")");
		string expr_subs = stack(*it);
		myReplace(condition, expr_find, expr_subs);
	}
}


void substitute_sync(string& condition){
	//printf("Substitute_syncs %s\n", condition.c_str());
	substitute_locks(condition);
	//printf("Substitute_syncs %s\n", condition.c_str());
	substitute_unlocks(condition);
	//printf("Substitute_syncs %s\n", condition.c_str());
	substitute_paths(condition);
	//printf("Substitute_syncs %s\n", condition.c_str());
	substitute_stores(condition);
	//printf("Substitute_syncs %s\n", condition.c_str());
	substitute_conds(condition);
	//printf("Substitute_syncs %s\n", condition.c_str());
	//printf("Substitute_syncs-----\n");
}


map<string, string> options_2;
void read_options_2(){

	FILE *file = fopen ( "/tmp/options", "r" );
	char line_c [ 128 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line_c, sizeof(line_c), file ) != NULL ){
		line_c[strlen(line_c)-1] = 0;
		string line = string(line_c);
		vector<string> tokens = tokenize(line, " ");
		options_2[ tokens[0] ] = tokens[1];
		
	}
	fclose ( file );
}

bool cmd_option_bool_2(string key){
	return options_2[key] == "true";
}


void dump_concurrency_constraints(FILE* file){
	
	read_options_2();
	if(cmd_option_bool_2("concurrency")) return;
	if(!cmd_option_bool_2("secuencialize")) return;

	load_concurrency_table(concurrency_table);

	stringstream condition;

	if(sync_points_and_locks.size() > 1)
		condition << "(and ";

	for( set<string>::iterator it = sync_points_and_locks.begin(); it != sync_points_and_locks.end(); it++ ){
		//printf("%s\n", it->c_str());
		condition << *it << " ";
	}

	if(sync_points_and_locks.size() > 1)
		condition << ")";

	string condition_s = condition.str();

	//printf("Concurrency_constraints_1::::::::::::::::::::  %s\n", condition_s.c_str());
	substitute_sync(condition_s);
	//substitute_sync(condition_s);
	//substitute_sync(condition_s);
	//printf("Concurrency_constraints_2::::::::::::::::::::  %s\n", condition_s.c_str());
	

	condition_s = "(assert " + condition_s + ")\n";

	fprintf(file, "%s", condition_s.c_str());

}

void dump_conditions( stringstream& sstr ){

	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if(!it->fuzzme)
			sstr << it->cond;
	}



}

void dump_check_sat(FILE* file){

	fprintf(file,"(check-sat)\n");

}

void dump_header(FILE* file){
	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");

}

int minval(string type){
	if(type == "Int32") return -(1 << 30);
	if(type == "Int16") return -(1 << 15);
	if(type == "Int8")  return -(1 << 8);
	if(type == "Int") return   -(1 << 30);
	if(type == "Pointer") return 0;

	printf("MinVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;
}

int maxval(string type){
	if(type == "Int32") return (1 << 30);
	if(type == "Int16") return (1 << 15);
	if(type == "Int8") return (1 << 8);
	if(type == "Int") return (1 << 30);
	if(type == "Pointer") return (1 << 30);

	printf("MaxVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;

}

void dump_type_limits(FILE* file){

	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = get_sized_type(it->name);

		if( get_type(it->name) != "Real" )
			fprintf(file,"(assert (and (>= %s %d) (< %s %d)))\n", name.c_str(), minval(type), name.c_str(), maxval(type) );
		
	}
}

void dump_tail(FILE* file){
	fprintf(file,"(exit)\n");
}

void dump_get_fuzz(FILE* file){
	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if(it->fuzzme)
			fprintf(file,"(get-value (%s)); \e[33m fuzzme \e[0m\n", it->cond.c_str() );
	}

}

int get_num_fuzzs(){

	int ret = 0;
	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if(it->fuzzme)
			ret++;
	}

	return ret;

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

void dump_get_free(FILE* file){


	for( set<NameAndPosition>::iterator it = variable_names.begin(); it != variable_names.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n", it->name.c_str(), it->name.c_str() );
	}
}

int get_num_fvars(){

	return variable_names.size();

}

string result_get(string get_str){

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

bool get_is_sat(string is_sat){
	if( is_sat == "sat" ) return true;
	else return false;
}

bool get_is_sat_with_fuzz( vector<string> fuzz_constraints ){

	for( vector<string>::iterator it = fuzz_constraints.begin(); it != fuzz_constraints.end(); it++ ){
		//printf("fuzz constraint %s \e[31m %s \e[0m\n", it->c_str(), result_get(*it).c_str() );
		if( result_get(*it) == "false" ){
			return false;
		}
	}
	
	return true;

}

string get_exclusion( vector<string> excluded_values ){

	string ret;
	for( vector<string>::iterator it = excluded_values.begin(); it != excluded_values.end(); it++ ){

		//printf("get_exclusion %s ---- %s\n", it->c_str(), result_get(*it).c_str() );
		//printf("get_exclusion %s\n", it->c_str());

		vector<string> tokens = tokenize(*it, "() ");
		string name = tokens[0];
		string value = result_get(*it);
		ret += "(= " + name + " " + value + ") ";
	}

	ret = "(not (and " + ret + "))";

	//printf("excl %s\n", ret.c_str() );

	return ret;
}

void insert_exclusion(string exclusion){

	exclusions.push_back(exclusion);
}

void clean_exclusions(){
	exclusions.clear();
}

void dump_exclusions(FILE* file){

	for( vector<string>::iterator it = exclusions.begin(); it != exclusions.end(); it++ ){
		fprintf(file,"(assert %s)\n", it->c_str() );
	}
	
	//fprintf(file,"(assert (> mem_8   0))\n" );
	//fprintf(file,"(assert (> mem_12  0))\n" );
	//fprintf(file,"(assert (< mem_8  16))\n" );
	//fprintf(file,"(assert (< mem_12 16))\n" );



}


bool sat;

void solve_problem(){

	vector<string> ret_vector;

	{

	sat = 0;


	clean_exclusions();

	for ( unsigned int i = 0; i < FUZZ_LIMIT; i++) {
	
		stringstream filename;
		filename << "z3_" << rand() << ".smt2";

		debug && printf("\e[31m filename solvable problem \e[0m %s\n", filename.str().c_str() );

		FILE* file = fopen(filename.str().c_str(), "w");


		read_options_2();

		dump_header(file);
		dump_variables(file);
		if(cmd_option_bool_2("secuencialize"))
			dump_sync_variables(file);
		dump_type_limits(file);
		dump_conditions(file);
		dump_concurrency_constraints(file);
		dump_exclusions(file);
		dump_check_sat(file);
		dump_get(file);
		dump_get_fuzz(file);
		dump_get_free(file);
		dump_tail(file);

		fclose(file);

		FILE *fp;
		stringstream command;
		char ret[SIZE_STR];
		
		command << "z3 " << filename.str();

		fp = popen(command.str().c_str(), "r");
		
		while (fgets(ret,SIZE_STR, fp) != NULL){
			ret[strlen(ret)-1] = 0;
			ret_vector.push_back(ret);
		}
		
		pclose(fp);

		int n_fuzzs = get_num_fuzzs();
		int n_fvars = get_num_fvars();


		string         sat_str       = ret_vector[0];
		vector<string> vect_for_fuzz = vector<string>(ret_vector.begin()+1, ret_vector.begin()+1+n_fuzzs);
		vector<string> vect_for_fvar = vector<string>(ret_vector.begin()+1+n_fuzzs, ret_vector.begin()+1+n_fuzzs+n_fvars);


		sat = 1;

		if( n_fuzzs == 0 ){
			sat = get_is_sat(sat_str);
			break;
		}

		if( !get_is_sat(sat_str) ){
			sat = 0;
			break;
		}

		if( !get_is_sat_with_fuzz(vect_for_fuzz) ){
			sat = 0;
		}

		if( !sat ){
			string exclusion = get_exclusion(vect_for_fvar);
			insert_exclusion(exclusion);
		} else {
			break;
		}

		if( i == FUZZ_LIMIT - 1 )
			debug && printf("\e[33m FUZZ_LIMIT exceeded \e[0m\n");

	}




	}

	if(sat){

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

	}

}

bool solvable_problem(){

	return sat;
	
}

void set_sat(bool _sat){
	sat = _sat;
}

void insert_variable(string name, string position){


	if(!check_mangled_name(name)) assert(0 && "Wrong name for insert_variable");


	if( name.find("constant") != string::npos )
		return;

	if( is_number(name) )
		return;

	//if(variables[name].contents.size() == 0)
		//return;
		
	debug && printf("\e[35m Insert_variable \e[0m name %s hint %s position %s\n", name.c_str(), variables[name].name_hint.c_str(), position.c_str() );

	if( PAUSE_ON_INSERT )
		getchar();

	if( EXIT_ON_INSERT )
		exit(0);

	NameAndPosition nandp = {name, position};
	variable_names.insert(nandp);

}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

float stof(string str){
	float ret;
	sscanf(str.c_str(), "%f", &ret);
	return ret;
}

void push_condition(string cond, string fn, vector<string> joints, bool fuzzme ){

	set<string> joints_set = set<string>(joints.begin(), joints.end());

	Condition condition = { cond, fn, joints_set, fuzzme };
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

	if (variables[name].type == "Int")
		return "Int";

	if (variables[name].type == "PointerTyID")
		return "Pointer";


	printf("name %s type %s\n", name.c_str(), variables[name].type.c_str() );

	assert(0 && "Unknown Type");

	return "Int";

}

string get_type(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for type");

	if(name.substr(0,9) == "constant" UNDERSCORE) return "IntegerTyID32";
	if( is_number(name) ){

		if( name.find(".") != string::npos )
			return "FloatTyID";
		else
			return "IntegerTyID32";
	}

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

	//printf("\e[33m is_number \e[0m %s\n", s.c_str() );

	if( s== "true" || s== "false") return true;

	if(s.substr(0,1) == "-") return is_number(s.substr(1));

	//printf("%s\n", s.substr(0,s.find(".")).c_str() );
	//printf("%s\n", s.substr(s.find(".")+1).c_str() );
	if( s.find(".") != string::npos ) return 
		is_number(s.substr(0,s.find("."))) &&
		is_number(s.substr(s.find(".")+1));


	if( s.find("e") != string::npos ) return 
		is_number(s.substr(0,s.find("e"))) &&
		is_number(s.substr(s.find("e")+1));

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

	if(input.substr(0,9) != "constant" UNDERSCORE &&
			input.substr(0,4) != "mem" UNDERSCORE &&
	 		input.substr(0,7) != "global" UNDERSCORE )
		myReplace(input, UNDERSCORE, "underscore" );


	if( input.substr(0,7) == "global" UNDERSCORE ){
		string postfix = input.substr(7);
		//printf("postfix %s\n", postfix.c_str() );
		myReplace(postfix, UNDERSCORE, "underscore");
		input = string("global") + UNDERSCORE + postfix;

		//printf("globalname %s\n", input.c_str());
	}

	if(input.find("constant") != string::npos ){
		int ini = 9;
		string interm = input.substr(ini);
		int len = interm.find(UNDERSCORE);
		string final = interm.substr(0, len);

		return final;
	} else if (input.substr(0,4) == "mem" UNDERSCORE ){
		return input;
	} else if (input.substr(0,7) == "global" UNDERSCORE ){
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
	if(!check_mangled_name(varname)) assert(0 && "Wrong src for get_is_propagated_constant");
	return variables[varname].is_propagated_constant;
}

void set_is_propagated_constant(string varname){
	if(!check_mangled_name(varname)) assert(0 && "Wrong src for set_is_propagated_constant");

	variables[varname].is_propagated_constant = true;

}

bool is_constant(string varname){
	if(!check_mangled_name(name(varname))) assert(0 && "Wrong src for is_constant");

	return varname.substr(0,9) == "constant" UNDERSCORE;

}

void setcontent(string varname, string content){
	if(!check_mangled_name(varname)) assert(0 && "Wrong src for setcontent");
	variables[varname].content = content;
}


bool is_forced_free(string position){
	if(!check_mangled_name(position)) assert(0 && "Wrong src for is_forced_free");

	if( forced_free_vars.find(position) != forced_free_vars.end() )
		return true;
	else 
		return false;

}

void load_forced_free_vars(){
	FILE *file = fopen ( "free_vars", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		forced_free_vars.insert(string(line));
	}
	fclose ( file );
	
}

void assign_instruction(string src, string dst, string fn_name){

	if(!check_mangled_name(name(src))) assert(0 && "Wrong src for assign");
	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for assign");


	debug && printf("\n\e[32m Assign_instruction %s = %s \e[0m\n", name(dst, fn_name).c_str(), name(src).c_str() );

	if( is_forced_free(name(src)) ){
		debug && printf("\e[32m Source is forced_free\e[0m\n");
		setcontent(name(src), "");
	}

	variables[ name(dst, fn_name) ].content = content( name(src) );

	//if( variables[name(dst)].type == "" ) assert(0 && "No type in dst");
	settype(name(dst, fn_name), get_type(name(src)));

	set_real_value( dst, realvalue(src), fn_name );


	if( (get_is_propagated_constant(name(src)) || is_constant(src)) && !is_forced_free(name(src)) )
		set_is_propagated_constant(name(dst, fn_name));

	if( get_fuzz_constr(name(src)) )
		set_fuzz_constr(name(dst, fn_name));


	//printf("srctree %s\n", get_offset_tree(name(src)).c_str());

	set_offset_tree(name(dst, fn_name), get_offset_tree(name(src)));


	//debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s\n", variables[ name(dst, fn_name) ].content.c_str(), variables[name(dst, fn_name)].type.c_str() );
	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d %d\n",
                 variables[ name(dst, fn_name) ].content.c_str(), variables[name(dst, fn_name)].type.c_str(), realvalue(dst).c_str(), 
		 get_is_propagated_constant(name(src)), get_is_propagated_constant(name(dst, fn_name)) );



}

bool implemented_operation(string operation){
	if(operation == "+" ) return true;
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
	if(operation == "X" ) return true;

	printf("operation %s\n", operation.c_str());
	return false;
}

string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

string wired_and( string op1, string op2, int nbits ){

	vector<string> z_bits;

	for ( unsigned int i = 0; i < nbits; i++) {
		int mod1 = ( 1 << i+1 );
		int mod2 = ( 1 << i   );

		string content1 = content(name(op1));
		string content2 = content(name(op2));
		
		//printf("content %s %s\n", content1.c_str(), content2.c_str() );

		stringstream x_bit_i;
		stringstream y_bit_i;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i << "(/ (- (mod " << content1 << " " << mod1 << ") (mod " << content1 << " " << mod2 << ")) " << mod2 << ")";
		y_bit_i << "(/ (- (mod " << content2 << " " << mod1 << ") (mod " << content2 << " " << mod2 << ")) " << mod2 << ")";

		z_bit_i << "(* " << x_bit_i.str() << " " << y_bit_i.str() << ")";

		z_bit_i_sh << "(* " << z_bit_i.str() << " " << mod2 << ")";

		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < nbits; i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;

}

string wired_xor( string op1, string op2, int nbits ){

	vector<string> z_bits;

	for ( unsigned int i = 0; i < nbits; i++) {
		int mod1 = ( 1 << i+1 );
		int mod2 = ( 1 << i   );

		string content1 = content(name(op1));
		string content2 = content(name(op2));
		
		//printf("content %s %s\n", content1.c_str(), content2.c_str() );

		stringstream x_bit_i;
		stringstream y_bit_i;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i << "(/ (- (mod " << content1 << " " << mod1 << ") (mod " << content1 << " " << mod2 << ")) " << mod2 << ")";
		y_bit_i << "(/ (- (mod " << content2 << " " << mod1 << ") (mod " << content2 << " " << mod2 << ")) " << mod2 << ")";

		z_bit_i << "(- (+ " << x_bit_i.str() << " " << y_bit_i.str() << ") (* 2 " << x_bit_i.str() << " " << y_bit_i.str() << "))";

		z_bit_i_sh << "(* " << z_bit_i.str() << " " << mod2 << ")";

		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < nbits; i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;

}

void set_fuzz_constr(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong dst for set_fuzz_constr");
	variables[name].fuzzme = true;

}

bool get_fuzz_constr(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong dst for get_fuzz_constr");
	return variables[name].fuzzme;

}

void binary_instruction(string dst, string op1, string op2, string operation){

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for binary_instruction");
	if(!check_mangled_name(name(op1))) assert(0 && "Wrong op1 for binary_instruction");
	if(!check_mangled_name(name(op2))) assert(0 && "Wrong op2 for binary_instruction");
	if(!implemented_operation(operation)) assert(0 && "Not implemented operation");

	debug && printf("\n\e[32m Binary_instruction %s = %s %s %s (%s %s)\e[0m\n",
			name(dst).c_str(), name(op1).c_str(), operation.c_str(), name(op2).c_str(),
		        get_type(name(op1)).c_str(), get_type(name(op2)).c_str() );


	stringstream content_ss;


	if( operation == "#" ){
		content_ss << "(not (= " << content( name(op1) ) << " " <<  content( name(op2) ) << "))";
	} else if (operation == "%") {
		content_ss << "(mod " << content( name(op1) ) << " " <<  content( name(op2) ) << ")";
	} else if (operation == "R" ) {

		if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		int exponent = stoi( op2.substr(9) );
		int factor = 1 << exponent;

		content_ss << "(/ " << content(name(op1)) << " " << factor << ")";

	} else if (operation == "L" ) {

		if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		int exponent = stoi( op2.substr(9) );
		int factor = 1 << exponent;

		content_ss << "(* " << content(name(op1)) << " " << factor << ")";

	} else if (operation == "Y" ) {
		content_ss << wired_and(op1, op2, 4);
		set_fuzz_constr(name(dst));
	} else if (operation == "X" ) {
		content_ss << wired_xor(op1, op2, 4);
		set_fuzz_constr(name(dst));
	} else {
		content_ss << "(" << operation << " " << content( name(op1) ) << " " <<  content( name(op2) ) << ")";
	}

	//debug && printf("\e[31m type \e[0m %s \e[31m op2 \e[0m %s \e[31m operation \e[0m %s\n", variables[name(op1)].type.c_str(), op2.c_str(), operation.c_str() );
	

	variables[name(dst)].content = content_ss.str();

	if( variables[name(op1)].type != "" )
		settype(name(dst), get_type(name(op1)));
	else
		settype(name(dst), get_type(name(op2)));


	if( get_fuzz_constr(name(op1)) || get_fuzz_constr(name(op2)) ){
		set_fuzz_constr(name(dst));
	}

	if( get_is_propagated_constant(name(op1)) && get_is_propagated_constant(name(op2)) ){
		set_is_propagated_constant(name(dst));
	}

	if( get_is_propagated_constant(name(op1)) && is_constant(op2) ){
		set_is_propagated_constant(name(dst));
	}

	if( is_constant(op1) && get_is_propagated_constant(name(op2)) ){
		set_is_propagated_constant(name(dst));
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

		stringstream result;
		if( get_type(name(dst)) == "Real" )
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		else if (get_type(name(dst)) == "Int")
			result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");

		set_real_value(dst, result.str());
	}

	if(operation == "-"){


		stringstream result;
		if( get_type(name(dst)) == "Real" )
			result << stof(realvalue(op1)) - stof(realvalue(op2));
		else if (get_type(name(dst)) == "Int")
			result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	}

	if(operation == "*"){

		stringstream result;
		if( get_type(name(dst)) == "Real" )
			result << stof(realvalue(op1)) * stof(realvalue(op2));
		else if (get_type(name(dst)) == "Int")
			result << stoi(realvalue(op1)) * stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	}


	if(operation == "/"){


		stringstream result;
		if( get_type(name(dst)) == "Real" )
			result << stof(realvalue(op1)) / stof(realvalue(op2));
		else if (get_type(name(dst)) == "Int")
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
		if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		int places = stoi( op2.substr(9) );

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


	if( variables[name(op1)].type != "" ) variables[name(dst)].type = variables[name(op1)].type;
	if( variables[name(op2)].type != "" ) variables[name(dst)].type = variables[name(op2)].type;


	if( variables[name(op1)].type == "bool" && op2 == "constant" UNDERSCORE "0" && operation == "#" ){
		debug && printf("\e[32m Propagation of bool constraint \e[0m\n");

		content_ss.str("");
		content_ss << content(name(op1));
		variables[name(dst)].content = content_ss.str();

		set_real_value(dst, realvalue(op1) );
	}




	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d\n",
                 variables[ name(dst) ].content.c_str(), variables[name(dst)].type.c_str(), realvalue(dst).c_str(),
		get_is_propagated_constant(name(dst)) );


}

int show_problem(){

	read_options_2();
	
	dump_header();
	dump_variables();
	if(cmd_option_bool_2("secuencialize"))
		dump_sync_variables();
	dump_type_limits();
	dump_conditions();
	dump_concurrency_constraints();
	dump_check_sat();
	dump_get();
	dump_get_fuzz();
	dump_tail();


		//dump_header(file);
		//dump_variables(file);
		//dump_type_limits(file);
		//dump_conditions(file);
		//dump_concurrency_constraints(file);
		//dump_exclusions(file);
		//dump_check_sat(file);
		//dump_get(file);
		//dump_get_fuzz(file);
		//dump_get_free(file);
		//dump_tail(file);








	stringstream filename; filename << "z3-" << rand() << ".smt2";

	debug && printf("\e[31m filename \e[0m %s\n", filename.str().c_str() );

	FILE* file = fopen(filename.str().c_str(), "w");

	dump_header(file);
	dump_variables(file);
	dump_type_limits(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_get(file);
	dump_get_fuzz(file);
	dump_tail(file);

	fclose(file);



	fflush(stdout);

	getchar();
}

void set_offset_tree( string varname, string tree ){
	//assert(check_mangled_name(varname) && "Incorrect name for set_offset_tree");
	//printf("set_offset_tree %s %s\n", varname.c_str(), tree.c_str() );
	variables[varname].tree = tree;
}

string get_offset_tree( string varname ){
	//assert(check_mangled_name(varname) && "Incorrect name for get_offset_tree");
	//printf("get_offset_tree %s %s\n", varname.c_str(), variables[varname].tree.c_str() );
	return variables[varname].tree;
}

void print_path_stack(){


	printf("\e[33m Path_stack \e[0m");
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		printf("%s", (*it)?"T":"F" );
	}
	printf("\n");

	printf("\e[33m Depth \e[0m %lu\n", path_stack.size());
	

}

