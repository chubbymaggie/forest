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

extern "C" void mutex_lock(char* mutex_name, char* sync_name);
extern "C" void mutex_unlock(char* mutex_name, char* sync_name);
extern "C" void begin_concurrency();

#endif /* end of include guard: _CONCURRENCY_H_ */

