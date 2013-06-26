/*
 * =====================================================================================
 * /
 * |     Filename:  measurement.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 09:22:48 AM
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


#include "measurement.h"

#define debug true

void begin_bb(char* name){

	debug && printf("\e[31m begin_bb %s \e[0m\n", name );
}

void end_bb(char* name){
	debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

void begin_sim(char* ){
	debug && printf("\e[31m Begin Simulation\e[0m\n" );
}

void BeginFn(char* _fn_name){


	debug && printf("\e[31m begin_fn %s \e[0m\n", _fn_name);


}

void end_sim(){

	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	
}

