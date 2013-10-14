/*
 * =====================================================================================
 * /
 * |     Filename:  database.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/13/2013 09:45:23 AM
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

#ifndef _DATABASE_H_
#define _DATABASE_H_

#include "sqlite3.h"
#include <string>
#include <sstream>
#include <map>
#include <utility>
#include <set>
#include <vector>
#include "operators.h"
#include "solver.h"
#include "utils.h"

using namespace std;


class Database {
public:
	Database ();
	virtual ~Database ();
	void insert_load(string pos);
	void start_database();

	void end_database();

	void create_tables();

	void insert_problem();
	set<pair<string, string> > get_sync_global_types();
	set<string> list_semaphores();
	set<vector<string> > get_paths_to(string dest);
	set<string> list_unlock_points();
	void load_stores(map<string, set<pair<string, string> > >& stores);
	void load_stacks(map<string, string>& stacks);
	set<string> list_sync_points();
	void load_concurrency_table(map<string, set<string> >& ret);
	set<string> list_store_sync_points();
	void insert_global_type(string name, string type);
	void insert_store(string pos, string content, string sync_name);

	void insert_sync_points(string sync_name, set<string> sync_points);
	void database_insert_concurrency(string lockunlock, string mutex_name, string sync_name, string conds);
	bool exists_in_concurrency(string lockunlock, string mutex_name, string sync_name, string conds);

private:
	sqlite3 *db;


	void drop_tables();
	string gethint(string name);
	int num_of_assertions() ;
	int num_of_variables() ;
	int num_of_mults();
	int num_of_divs();
	int num_of_sums();
	int num_of_subs();

	//static int callback(void *NotUsed, int argc, char **argv, char **azColName);


	bool yet_covered();

	void create_concurrency_tables();
	void drop_concurrency_tables();

	bool exists_in_global_types(string name);
	bool exists_in_sync(string syncname);

	
};




#endif /* end of include guard: _DATABASE_H_ */
