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

extern "C" void pivot_hint(char*);

int main() {

	int a;
	int b = 2*a;

	pivot_hint((char*)"main_register_b");

	b = b + 2;

	if(b)
		return 1;
	else
		return 0;
	
}
