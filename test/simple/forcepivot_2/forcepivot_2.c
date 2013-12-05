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

extern "C" void pivot_variable(char*);

int function( int x ){


	pivot_variable((char*)"Z8functioni_registerunderscorex"); // x

	x = x + 2;

	if(x == 1)
		return x;
	else
		return x;
}

int main() {

	int a;

	a = 2*a;

	int b = 2*function(a);

	if( b == 2 )
		return 1;
	else
		return 0;
	
}
