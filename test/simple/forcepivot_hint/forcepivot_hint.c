/*
 * =====================================================================================
 * /
 * |     Filename:  forcepivot.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/06/2013 02:42:59 PM
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

#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 

extern "C" void pivot_hint(char*);

int main() {

	int a;


#ifdef KLEE
	klee_make_symbolic(&a, sizeof(a), "a");
#endif

	int b = 2*a;

#ifndef KLEE
	pivot_hint((char*)"main_register_b");
#endif

	b = b + 2;

	if(b)
		return 1;
	else
		return 0;
	
}
