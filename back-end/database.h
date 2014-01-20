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


typedef struct NameAndType {
	string name;
	string type;
} NameAndType;


class Database {
public:
	void insert_model_entry(string name,string free_vars, string content, string path);
	set<string> global_stores(string sync_name);
	set<string> global_variables();
	string lockunlock(string sync_point);
	string semaphore_of(string sync_point);
	set<string> list_lock_points();
	set<NameAndType> get_shared_vars();
	Database ();
	virtual ~Database ();

	/**
	 * @brief Opens the database
	 */
	void start_database();

	/**
	 * @brief Closes the database
	 */
	void end_database();


	/**
	 * @brief Creates needed tables
	 */
	void create_tables();


	/**
	 * @brief Inserts a problem in the database 
	 * Called by the br_instr_cond operator
	 */
	void insert_problem();

	/**
	 * @brief returns a list with the type of all shared variables
	 */
	set<pair<string, string> > get_sync_global_types();

	/**
	 * @brief returns a list of all semaphores
	 */
	set<string> list_semaphores();

	/**
	 * @brief returns a list with all the paths to a given basic_block
	 */
	set<vector<string> > get_paths_to(string dest);

	/**
	 * @brief Returns a list of all the sync_points
	 *
	 * @return 
	 */
	set<string> list_unlock_points();

	/**
	 * @brief Fills a list with all the stores (shared variables)
	 *
	 * @param stores
	 */
	void load_stores(map<string, set<pair<string, string> > >& stores);

	/**
	 * @brief Fills a list with the conditions needed to reach each sync point
	 *
	 * @param stacks
	 */
	void load_stacks(map<string, string>& stacks);

	/**
	 * @brief Fills a map indicating which sync_point unlocks each semaphore
	 *
	 * @param ret
	 */
	void load_concurrency_table(map<string, set<string> >& ret);

	/**
	 * @brief Inserts a new global type
	 *
	 * @param name position of the shared variable
	 * @param type type
	 * @param position position in the information execution
	 */
	void insert_global_type(string name, string type, string position);

	/**
	 * @brief Inserts a new entry in the database indicating that a shared variable has been written
	 *
	 * @param pos position in memory
	 * @param content content
	 * @param sync_name name of the synchronization name where the variable is written
	 */
	void insert_store(string pos, string content, string sync_name);

	/**
	 * @brief inserts a load in the database
	 *
	 * @param pos Position accessed by the load
	 */
	void insert_load(string pos);

	/**
	 * @brief Inserts in the database the preceding synchronization points of a given one
	 *
	 * @param sync_name name of the sync_point
	 * @param sync_points name of the preceding ones
	 */
	void insert_sync_points(string sync_name, set<string> sync_points);

	/**
	 * @brief Inserts information about concurrency in concurrency table
	 *
	 * @param lockunlock whether the sync_point is a lock or unlocking one
	 * @param mutex_name name of the mutex that is locked/unlocked
	 * @param sync_name name of the syncrhonization point
	 * @param conds stacks of conditions needed to reach this point
	 */
	void database_insert_concurrency(string lockunlock, string mutex_name, string sync_name, string conds);

	/**
	 * @brief returns all synchronization names
	 */
	set<string> list_sync_points();

	/**
	 * @brief return all synchronization names
	 */
	set<string> list_store_sync_points();



void insert_measurement(string, string);
void start_database_measurement();
void end_database_measurement();
void insert_problem_measurement();


private:
	int count_in_conds(string op);
	sqlite3 *db;



	/**
	 * @brief Removes all tables from database
	 */
	void drop_tables();

	/**
	 * @brief Number of assertions of a given problem (for statistics)
	 */
	int num_of_assertions() ;

	/**
	 * @brief Number of variables of a given problem (for statistics)
	 */
	int num_of_variables() ;

	/**
	 * @brief Number of multiplications of a given problem (for statistics)
	 */
	int num_of_mults();

	/**
	 * @brief Number of divisions of a given problem (for statistics)
	 */
	int num_of_divs();

	/**
	 * @brief Number of sums of a given problem (for statistics)
	 */
	int num_of_sums();

	/**
	 * @brief Number of substractions of a given problem (for statistics)
	 *
	 * @return 
	 */
	int num_of_subs();

	/**
	 * @brief Creates tables for concurrency
	 */
	void create_concurrency_tables();

	/**
	 * @brief removes concurrency tables
	 */
	void drop_concurrency_tables();

	/**
	 * @brief returns true if the information is already present in the database
	 */
	bool exists_in_global_types(string name);

	/**
	 * @brief Returns true if the information is already present in the database
	 */
	bool exists_in_sync(string syncname, set<string> sync_points);

	/**
	 * @brief returns true if the information is already present in the database
	 */
	bool exists_in_stores(string pos, string content, string sync_name);

	/**
	 * @brief Returns one if the information is already present in the database
	 */
	bool exists_in_concurrency(string lockunlock, string mutex_name, string sync_name, string conds);





	
};




#endif /* end of include guard: _DATABASE_H_ */
