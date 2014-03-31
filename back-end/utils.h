/*
 * =====================================================================================
 * /
 * |     Filename:  utils.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/12/2013 03:55:48 AM
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


#ifndef _UTILS_H_
#define _UTILS_H_

#include <string>
#include <vector>
#include <sstream>
#include <stdio.h>
#include <assert.h>

using namespace std;

int get_size(string type);

int get_ini_elem(int nelem_target, string offset_tree);

string close_str(string offset_tree);

string trimpar(string str);

bool has_index(string offset_tree, int index);

int get_offset(vector<string> indexes, string offset_tree, string* remaining_tree);

void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr);

string itos(int i);
bool is_number(const std::string& s);
int count(string name, string character);


vector<string> tokenize(const string& str,const string& delimiters);

int stoi(string str);
short stos(string str);
short stoc(string str);
float stof(string str);
string locknames(string condition);
string binary_rep(int n);

#endif /* end of include guard: _UTILS_H_ */
