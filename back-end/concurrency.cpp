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

#include <stdio.h>
#include "concurrency.h"
#include "solver.h"
#include <sstream>

using namespace std;

void mutex_lock(char* mutex_name, char* sync_name){

	printf("mutex_lock %s %s\n", mutex_name, sync_name);

	//stringstream conds;
	//dump_conditions(conds);
	//printf("-----------------------------------\n");
	dump_conditions();
	//printf("conds %s\n", conds.str().c_str() );
	//printf("-----------------------------------\n");


}

void mutex_unlock(char* mutex_name, char* sync_name){

	printf("mutex_unlock %s %s\n", mutex_name, sync_name);

	//stringstream conds;
	//dump_conditions(conds);
	//printf("-----------------------------------\n");
	dump_conditions();
	//printf("conds %s\n", conds.str().c_str() );
	//printf("-----------------------------------\n");

}

