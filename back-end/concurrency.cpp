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
	sync_points_and_locks.insert( "(" + lockunlock + "_" + mutex_name + ")" );
}

void Concurrency::get_conditions_to_reach_here(string& ret){
	
	stringstream ret_ss;

	ret_ss << "(and ";
	for( set<string>::iterator it = sync_points_and_locks.begin(); it != sync_points_and_locks.end(); it++ ){
		ret_ss << *it << " ";
	}
	ret_ss << ")";

	ret = ret_ss.str();
	

}

void Concurrency::mutex_lock_constraints(char* _mutex_name, char* _sync_name){

	debug && printf("mutex_lock_constraints %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

	insert_sync_point("lock", sync_name, mutex_name);
	

}

void Concurrency::mutex_unlock_constraints(char* _mutex_name, char* _sync_name){

	debug && printf("mutex_unlock_constraints %s %s\n", _mutex_name, _sync_name);

	string mutex_name = string(_mutex_name);
	string sync_name = string(_sync_name);

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

	debug && printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(addr).c_str(),
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
		debug && printf("if_concurrency dst %s src %s\n", dst.c_str(), src.c_str());
		if(is_shared(dst))
			update_store(dst, solver->content(name(src)));
	}



	solver->assign_instruction(name(src),name(dst));

	debug && printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",name(src).c_str(), name(addr).c_str(),
			                                           name(src).c_str(), realvalue(src).c_str(),
								   name(addr).c_str(), realvalue(addr).c_str(),
								   name(dst).c_str(), realvalue(dst).c_str() );

}


#undef name 
#undef realvalue

