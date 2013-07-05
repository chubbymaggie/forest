/*
 * =====================================================================================
 * /
 * |     Filename:  measurement.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 09:24:49 AM
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

#ifndef _MEASUREMENT_H_
#define _MEASUREMENT_H_

#include "database_measurement.h"
#include <stdio.h>
#include <set>
#include <string>
#include <vector>
#include <sstream>
#include <string.h>
#include <assert.h>

/**
 * @brief  Begin basic Block
 *
 * @param name: Name of the basic block
 */
extern "C" void begin_bb(char* a);

/**
 * @brief End basic block
 *
 * @param name
 */
extern "C" void end_bb(char* a);

/**
 * @brief Function that is called at the begining of simulation
 */
extern "C" void begin_sim(char*, char*);

/**
 * @brief Function that is called at the end of simulation
 */
extern "C" void end_sim();

extern "C" void BeginFn(char* _fn_name);
extern "C" void EndFn();

extern "C" void br_instr_cond(bool value);

extern "C" int vector_int(char*);
extern "C" char vector_char(char*);
extern "C" short vector_short(char*);

#endif /* end of include guard: _OPERATORS_H_ */

