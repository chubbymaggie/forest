/*
 * =====================================================================================
 * /
 * |     Filename:  database_measurement.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 11:54:38 AM
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

#ifndef _DATABASE_MEASUREMENT_H_
#define _DATABASE_MEASUREMENT_H_

#include "sqlite3.h"
#include <string>
#include <sstream>
#include <map>
#include <utility>
#include <set>
#include <vector>
#include <stdio.h>

using namespace std;

static int callback(void *NotUsed, int argc, char **argv, char **azColName);
void insert_measurement(string, string);
void start_database();
void end_database();


#endif /* end of include guard: _DATABASE_H_ */
