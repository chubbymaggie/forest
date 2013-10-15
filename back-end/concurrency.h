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
#include "database.h"
#include "solver.h"
#include <sstream>

#include "solver.h"

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

	/**
	 * @brief called by the wrapper when a mutex is locked
	 *
	 * @param mutex_name name of the mutex
	 * @param sync_name name of the synchronization point
	 */
	void mutex_lock(char* mutex_name, char* sync_name);

	/**
	 * @brief Called by the wrapper when a mutex is unlocked
	 *
	 * @param mutex_name name of the mutex
	 * @param sync_name name of the synchronization point
	 */
	void mutex_unlock(char* mutex_name, char* sync_name);

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
private:


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
	bool debug;

	/**
	 * @brief Inserts types of shared variables (stores)
	 */
	void insert_global_types();

	/**
	 * @brief dumps the synchronization table at the end of the simulation
	 */
	void dump_sync_table();
	
};


#endif /* end of include guard: _CONCURRENCY_H_ */

