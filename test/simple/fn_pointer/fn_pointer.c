/*
 * =====================================================================================
 * /
 * |     Filename:  fn_pointer.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/18/2013 04:26:50 PM
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


int funcion(int a){
	return 1-a;
}


int main() {
	int (*fn)(int a) = funcion;

	int b;
	if( fn(b) )
		return 0;
	else
		return 1;
}
