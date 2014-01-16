/*
 * =====================================================================================
 * /
 * |     Filename:  forest.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/16/2013 04:00:43 AM
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


#ifndef _FOREST_H_
#define _FOREST_H_

#include "./tinyxml.h"
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <fstream>
#include <iostream>

using namespace std;

void make_bc();
void run();
void test();
void clean();
void final();
void measure_coverage();
void check_coverage();
void options_to_file();
void set_option( string key, string value );
void do_klee();
void minimal_test_vectors_to_db();
void db_command(string command);
void get_result();
void vim();


#endif /* end of include guard: _FOREST_H_ */
