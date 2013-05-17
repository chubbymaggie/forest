/*
 * =====================================================================================
 * /
 * |     Filename:  operators.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/15/2013 05:27:48 PM
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

extern "C" void binary_op(char*, char*, char*);
extern "C" void load_instr(char*, char*);
extern "C" void store_instr(char*, char*);

void binary_op(char* a, char* b, char* c){
	printf("operación binaria %s %s %s\n", a, b, c);
}

void load_instr(char* a, char*b){
	printf("load instruction %s %s\n", a, b);
}

void store_instr(char* a, char*b){
	printf("store instruction %s %s\n", a, b);
}
