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

	void mutex_lock(char* mutex_name, char* sync_name);
	void mutex_unlock(char* mutex_name, char* sync_name);

	void begin_concurrency();
	void insert_global_types();
	void dump_sync_table();
	void end_concurrency();

private:
set<MutexInfo> mutexinfos;
	
};


#endif /* end of include guard: _CONCURRENCY_H_ */

