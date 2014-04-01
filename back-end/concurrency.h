/*
 * =====================================================================================
 * /
 * |     Filename:  concurrency.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/30/2013 03:53:06 PM
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


#ifndef _CONCURRENCY_H_
#define _CONCURRENCY_H_

#include <stdio.h>
#include <sstream>
#include <set>
#include <map>

using namespace std;

typedef struct MutexInfo {
	string lockunlock;
	string mutex_name;
	string sync_name;
	string conds;
} MutexInfo;

inline bool operator<(const MutexInfo& lhs, const MutexInfo& rhs) {
  return (lhs.lockunlock + lhs.mutex_name + lhs.sync_name + lhs.conds) < (rhs.lockunlock + rhs.mutex_name + rhs.sync_name + rhs.conds);
}


class Concurrency {
public:
	Concurrency ();
	virtual ~Concurrency ();

	void dump_remaining_variables( set<struct NameAndPosition> free_variables, FILE* file = stdout );

	/**
	 * @brief called by the wrapper when a mutex is locked
	 *
	 * @param mutex_name name of the mutex
	 * @param sync_name name of the synchronization point
	 */
	void mutex_lock_info(char* mutex_name, char* sync_name);

	/**
	 * @brief Called by the wrapper when a mutex is unlocked
	 *
	 * @param mutex_name name of the mutex
	 * @param sync_name name of the synchronization point
	 */
	void mutex_unlock_info(char* mutex_name, char* sync_name);

	/**
	 * @brief Called by the wrapper at the beginning of the simulation
	 */
	void begin_concurrency();

	/**
	 * @brief Called by the wrapper at the end of simulation
	 */
	void end_concurrency();

	/**
	 * @brief updates the store information
	 *
	 * @param dst memory to be written
	 * @param content content to be written
	 */
	void update_store(string dst, string content);

	void mutex_lock_constraints(char* _mutex_name, char* _sync_name);
	void mutex_unlock_constraints(char* _mutex_name, char* _sync_name);



	void store_instr(char* _src, char* _addr);
	void load_instr(char* _dst, char* _addr);

	void alloca_instr(char* _reg, char* _subtype);

private:

	string last_sync;
	void substitute_global(string& condition);
	string stack(string sync_point);
	map<string, set<pair<string, string> > > stores;
	map<string, string> stacks;
	void substitute_conds(string& condition);
	string and_stores(string sync_point);
	void substitute_stores(string& condition);
	void substitute_paths(string& condition);
	string or_paths(string dest);
	void substitute_unlocks(string& condition);

	map<string, set<string> > concurrency_table;


	set<string> unlock_points(string mutex);
	string or_unlocking(string condition, string mutex);
	void substitute_locks(string& condition);
	void propagate_constraints(string& conditions);
	void get_conditions_to_reach_here(string& ret);


	set<string> sync_points_and_locks;
	void insert_sync_point(string lockunlock, string sync_name, string mutex_name);

	/**
	 * @brief Information about lock, mutex_name, sync_name and stack when a synchronization point 
	 * is reached
	 */
	set<MutexInfo> mutexinfos;

	/**
	 * @brief Names of all the sync_points reached
	 */
	set<string> sync_points;

	/**
	 * @brief map with the content of all stores
	 */
	map<string, string> map_pos_to_last_store;

	/**
	 * @brief inserts all stores in the database, associated with a synchronization point
	 *
	 * @param sync_name
	 */
	void insert_stores(string sync_name);
	//bool debug;

	/**
	 * @brief Inserts types of shared variables (stores)
	 */
	void insert_global_types();

	/**
	 * @brief dumps the synchronization table at the end of the simulation
	 */
	void dump_sync_table();


	bool is_shared(string name);

	set<string> locales;

};


#endif /* end of include guard: _CONCURRENCY_H_ */

