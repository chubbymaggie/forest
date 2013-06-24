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

using namespace std;


static int callback(void *NotUsed, int argc, char **argv, char **azColName);

void start_database();

void end_database();

void create_tables();

void insert_problem();

bool yet_covered();


#endif /* end of include guard: _DATABASE_H_ */
