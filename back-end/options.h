/*
 * =====================================================================================
 * /
 * |     Filename:  options.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/12/2013 03:43:52 AM
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

#ifndef _OPTIONS_H_
#define _OPTIONS_H_

#include <string>
#include <map>
#include <stdio.h>
#include "utils.h"
#include <string.h>

using namespace std;


class Options {
public:
	Options ();
	virtual ~Options ();
	void read_options();
	bool cmd_option_bool(string key);

private:
	map<string, string> options;
	
};



#endif /* end of include guard: _OPTIONS_H_ */
