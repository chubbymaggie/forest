/*
 * =====================================================================================
 * /
 * |     Filename:  concurrency.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/30/2013 03:52:15 PM
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

#include "concurrency.h"
#define debug true

using namespace std;

extern Solver* solver;
extern Database* database;
extern Options* options;
extern Operators* operators;

Concurrency::Concurrency(){;}
Concurrency::~Concurrency(){;}

void Concurrency::insert_global_types(){
	

	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){

		string name = it->first;
		string type = solver->get_type(name);
		string position = solver->get_position(name);

		database->insert_global_type(name,type,position);
	}
	
}

void Concurrency::alloca_instr(char* _reg, char* _subtype){
	debug && printf("concurrency_alloca_instr %s %s\n", _reg, _subtype);
	string reg = string(_reg);
	string subtype = string(_subtype);
	string given_addr = solver->realvalue(operators->name(reg));
	int size = get_size(subtype);
	debug && printf("given address %s size %d\n", given_addr.c_str(), size);

	int start = stoi(given_addr);
	int end = start + size;

	for ( unsigned int i = start; i < end; i++) {
		stringstream pos; pos << "mem_" << i;
		debug && printf("pos %s is local\n", pos.str().c_str());
		locales.insert(pos.str());
	}

}

bool Concurrency::is_shared(string name){

	bool ret = locales.find(name) == locales.end();

	debug && printf("is_shared %s %d\n", name.c_str(), ret);

	return ret;
}

void Concurrency::insert_stores(string sync_name){

	for( map<string,string>::iterator it = map_pos_to_last_store.begin(); it != map_pos_to_last_store.end(); it++ ){
		database->insert_store(it->first, it->second, sync_name );
	}

}

void Concurrency::mutex_lock_info(char* _mutex_name, char* _sync_name){

	debug && printf("mutex_lock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	insert_stores(sync_name);
	insert_global_types();
	map_pos_to_last_store.clear();

	stringstream conds;
	solver->dump_conditions(conds);
	//string translated_conds = translate_global(conds.str());

	MutexInfo mutexinfo = {"lock", mutex_name, sync_name,conds.str()};
	mutexinfos.insert(mutexinfo);

	sync_points.insert(sync_name);

	database->insert_sync_points(sync_name, sync_points);

}

void Concurrency::mutex_unlock_info(char* _mutex_name, char* _sync_name){


	debug && printf("mutex_unlock %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	insert_stores(sync_name);
	insert_global_types();
	map_pos_to_last_store.clear();

	stringstream conds;
	solver->dump_conditions(conds);
	//string translated_conds = translate_global(conds.str());

	MutexInfo mutexinfo = {"unlock", mutex_name, sync_name,conds.str()};
	mutexinfos.insert(mutexinfo);

	sync_points.insert(sync_name);

	database->insert_sync_points(sync_name, sync_points);

}

void Concurrency::dump_sync_table(){

	for( set<MutexInfo>::iterator it = mutexinfos.begin(); it != mutexinfos.end(); it++ ){
		database->database_insert_concurrency(it->lockunlock, it->mutex_name, it->sync_name, it->conds);
	}
	
}


void Concurrency::begin_concurrency(){
	//options->read_options();
	//debug = options->cmd_option_bool("verbose");
}


void Concurrency::end_concurrency(){
	dump_sync_table();
}

void Concurrency::update_store(string dst, string content){

	string hint = solver->get_name_hint(dst);
	map_pos_to_last_store[hint] = content;
}

void Concurrency::insert_sync_point(string lockunlock, string sync_name, string mutex_name){
	printf("Insert_sync_point %s %s %s\n", lockunlock.c_str(), sync_name.c_str(), mutex_name.c_str());
	sync_points_and_locks.insert( "(" + lockunlock + "_" + sync_name + ")" );
}

void Concurrency::get_conditions_to_reach_here(string& ret){

	printf("\e[31m Get_conditions_to_reach_here \e[0m %lu\n", sync_points_and_locks.size() );

	if(sync_points_and_locks.size() == 0){
		ret = "true";
		return;
	}

	stringstream ret_ss;

	ret_ss << "(and ";
	for( set<string>::iterator it = sync_points_and_locks.begin(); it != sync_points_and_locks.end(); it++ ){
		string condition = *it;
		if(condition.substr(0,6) == "(lock_")
			ret_ss << condition << " ";
	}
	ret_ss << ")";

	ret = ret_ss.str();

	printf("\e[31m Get_conditions_to_reach_here \e[0m %s\n", ret.c_str() );
	

}


set<string> Concurrency::unlock_points(string mutex){

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



string Concurrency::or_unlocking(string condition, string mutex){

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

void Concurrency::substitute_locks(string& condition){

	//set<string> mutexes = database->list_semaphores();
	set<string> mutexes = database->list_lock_points();
	//mutexes.insert("a");
	//mutexes.insert("b");
	//mutexes.insert("c");

	for( set<string>::iterator it = mutexes.begin(); it != mutexes.end(); it++ ){
		string expr_find = string("(lock_") + (*it) + string(")");
		string semaphore = database->semaphore_of(*it);
		string expr_subs = or_unlocking(condition, semaphore);
		myReplace(condition, expr_find, expr_subs);
	}
	
	

}


void Concurrency::substitute_unlocks(string& condition){

	//printf("substitute_unlocks\n");

	set<string> unlock_points = database->list_unlock_points();

	//printf("unlock_points.size %lu\n", unlock_points.size());
	
	for( set<string>::iterator it = unlock_points.begin(); it != unlock_points.end(); it++ ){
		//printf("unlock_point %s\n", it->c_str());
		string expr_find = string("(unlock_") + (*it) + string(")");
		string expr_subs = or_paths(*it);
		myReplace(condition, expr_find, expr_subs);
	}
	

}

string Concurrency::or_paths(string dest){

	//printf("or_paths %s\n", dest.c_str());

	//if(dest == "bb")    return "(de)";
	//if(dest == "bb1")   return "(df)";
	//if(dest == "bb2")   return "(deg o dfg)";
	//if(dest == "bb4")   return "(bb4)";
	//if(dest == "entry") return "(1)";
	//return "()";

	set<vector<string> > paths = database->get_paths_to(dest);

	//printf("dest %s path num %lu\n",dest.c_str(), paths.size());

	stringstream ret;
	if(paths.size() > 1)
		ret << "(or ";
	for( set<vector<string> >::iterator it = paths.begin(); it != paths.end(); it++ ){
		vector<string> path = (*it);
		if(path.size() > 1)
			ret << "(and ";
		for( vector<string>::iterator it2 = path.begin(); it2 != path.end(); it2++ ){
			string cond = *it2;
			string lockunlock = database->lockunlock(cond);
			if( lockunlock == "unlock" )
				ret << "(statepath_" << cond << ")" << " ";
		}
		if(path.size() > 1)
			ret << ") ";
	}
	if(paths.size() > 1)
		ret << ")";

	//return "(" + dest + ")";
	return ret.str();
	
}

void Concurrency::substitute_paths(string& condition){

	//printf("substitute_unlocks\n");

	set<string> unlock_points = database->list_unlock_points();

	//printf("unlock_points.size %lu\n", unlock_points.size());
	
	for( set<string>::iterator it = unlock_points.begin(); it != unlock_points.end(); it++ ){
		//printf("unlock_point %s\n", it->c_str());
		string expr_find = string("(statepath_") + (*it) + string(")");
		string expr_subs = "(and (stores_" + (*it) + ") (conds_" + (*it) + "))";
		myReplace(condition, expr_find, expr_subs);
	}

}


void Concurrency::substitute_stores(string& condition){

	//printf("substitute_stores\n");

	set<string> sync_points = database->list_store_sync_points();

	//printf("sync_points.size %lu\n", sync_points.size());
	
	for( set<string>::iterator it = sync_points.begin(); it != sync_points.end(); it++ ){
		//printf("sync_store_point %s\n", it->c_str());
		string expr_find = string("(stores_") + (*it) + string(")");
		string expr_subs = and_stores(*it);
		myReplace(condition, expr_find, expr_subs);
	}
}


string Concurrency::and_stores(string sync_point){

	database->load_stores(stores);
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


void Concurrency::substitute_conds(string& condition){

	//printf("substitute_conds\n");

	set<string> sync_points = database->list_sync_points();

	//printf("sync_points.size %lu\n", sync_points.size());
	
	for( set<string>::iterator it = sync_points.begin(); it != sync_points.end(); it++ ){
		//printf("sync_point %s\n", it->c_str());
		string expr_find = string("(conds_") + (*it) + string(")");
		string expr_subs = stack(*it);
		myReplace(condition, expr_find, expr_subs);
	}
}



string Concurrency::stack(string sync_point){

	database->load_stacks(stacks);
	return stacks[sync_point];

	//if(sync_point == "entry") return "(true)";
	//if(sync_point == "bb")    return "(= mem_123 25)";
	//if(sync_point == "bb4")   return "(not (= mem_123 25))";
	//if(sync_point == "bb2")   return "(true)";
	//if(sync_point == "bb1")   return "(not (= mem_123 12))";
	//return "";
	
}

void Concurrency::substitute_global(string& condition){

	set<NameAndType> globals = database->get_shared_vars();

	for( set<NameAndType>::iterator it = globals.begin(); it != globals.end(); it++ ){
		string name = it->name;

		myReplace(condition, name, name + "_pivot_" + last_sync);

	}
	

	//myReplace(condition, "global_j", "global_j_b");
}

void Concurrency::propagate_constraints(string& condition){

	database->load_concurrency_table(concurrency_table);

	printf("Substitute_syncs %s\n", locknames(condition).c_str());
	substitute_locks(condition);
	printf("Substitute_syncs %s\n", locknames(condition).c_str());
	substitute_unlocks(condition);
	printf("Substitute_syncs %s\n", locknames(condition).c_str());
	substitute_paths(condition);
	printf("Substitute_syncs %s\n", locknames(condition).c_str());
	substitute_stores(condition);
	printf("Substitute_syncs %s\n", locknames(condition).c_str());
	substitute_conds(condition);
	printf("Substitute_syncs %s\n", locknames(condition).c_str());
	substitute_global(condition);
	printf("Substitute_syncs %s\n", locknames(condition).c_str());
	printf("Substitute_syncs-----\n");

	myReplace(condition, "(and   true )", "");
	myReplace(condition, "(and    )","true");
	myReplace(condition, "  "," ");
	myReplace(condition, "  "," ");
	myReplace(condition, "  "," ");
	myReplace(condition, "(and )","true");

}



void Concurrency::dump_remaining_variables( set<NameAndPosition> free_variables, FILE* file ){

	return;

	
	set<NameAndType> shared_vars = database->get_shared_vars();


	//printf("shared_vars.size() %lu\n", shared_vars.size() );

	for( set<NameAndType>::iterator it = shared_vars.begin(); it != shared_vars.end(); it++ ){

		//printf("name %s type %s\n", it->name.c_str(), it->type.c_str());

		bool found = false;
		for( set<NameAndPosition>::iterator it2 = free_variables.begin(); it2 != free_variables.end(); it2++ ){
			if(it->name == it2->name)
				found = true;
		}

		if(!found)
			solver->dump_variable(it->name, it->type, file);
		

	}
	

}

void Concurrency::mutex_lock_constraints(char* _mutex_name, char* _sync_name){

	debug && printf("mutex_lock_constraints %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	last_sync = sync_name;

	insert_sync_point("lock", sync_name, mutex_name);

	string sync_conditions;
	get_conditions_to_reach_here(sync_conditions);

	propagate_constraints(sync_conditions);

	if( sync_conditions != "true"){
		string actual_function = operators->get_actual_function();
		string actual_bb = operators->get_actual_bb();
		vector<string> empty; empty.push_back(actual_bb);
		solver->push_condition(sync_conditions, actual_function, empty);

	}

	set<string> global_stores = database->global_stores(sync_name);

	for( set<string>::iterator it = global_stores.begin(); it != global_stores.end(); it++ ){
		string variable = *it;
		solver->pivot_variable(variable, sync_name);
	}

}

void Concurrency::mutex_unlock_constraints(char* _mutex_name, char* _sync_name){

	debug && printf("mutex_unlock_constraints %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	last_sync = sync_name;

	insert_sync_point("unlock", sync_name, mutex_name);

}

#define UNDERSCORE "_"

#define name(A) operators->name(A)
#define realvalue(A) solver->realvalue(name(A))

void Concurrency::load_instr(char* _dst, char* _addr){

	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem" UNDERSCORE + realvalue(addr);


	//if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for load");
	//if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for load");

	if(options->cmd_option_bool("secuencialize")){
		database->insert_load(src);
	}

	solver->assign_instruction(name(src),name(dst));


	if(options->cmd_option_bool("concurrency")){
		debug && printf("load_concurrency dst %s src %s\n", dst.c_str(), src.c_str());
		if(is_shared(src)){
			printf("src_of_load_is_shared %s %s\n", solver->get_name_hint(src).c_str(), solver->get_type(src).c_str() );
			string name = solver->get_name_hint(src);
			string type = solver->get_type(src);
			database->insert_global_type(name, type, "");
		}
	}





	debug && printf("\e[31m Concurrency load instruction %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(addr).c_str(),
								    name(addr).c_str(), realvalue(addr).c_str(),
								    name(src).c_str(), realvalue(src).c_str(),
							            name(dst).c_str(), realvalue(dst).c_str()
								    );
	//exit(0);

}

void Concurrency::store_instr(char* _src, char* _addr){

	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem" UNDERSCORE + realvalue(string(_addr)) ;




	//if(!check_mangled_name(name(src))) assert(0 && "Wrong src for store");
	//if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for store");
	//if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for store");


	if(options->cmd_option_bool("secuencialize")){
		//solver->insert_variable(name(dst), operators->get_actual_function() + UNDERSCORE + solver->get_name_hint(name(dst)) );
	
		stringstream stack;
		solver->dump_conditions(stack);
	}

	if(options->cmd_option_bool("concurrency")){
		debug && printf("store_concurrency dst %s src %s\n", dst.c_str(), src.c_str());
		if(is_shared(dst))
			update_store(dst, solver->content(name(src)));
	}



	solver->assign_instruction(name(src),name(dst));

	debug && printf("\e[31m Concurrency store instruction %s %s\e[0m %s %s %s %s %s %s\n",name(src).c_str(), name(addr).c_str(),
			                                           name(src).c_str(), realvalue(src).c_str(),
								   name(addr).c_str(), realvalue(addr).c_str(),
								   name(dst).c_str(), realvalue(dst).c_str() );

}


#undef name 
#undef realvalue

