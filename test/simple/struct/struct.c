/*
 * =====================================================================================
 * /
 * |     Filename:  struct.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/07/2013 07:45:56 AM
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

struct Estructura {
	int entero1;
	int entero2;
	struct estructura3{
		int entero4;
		int entero5;
	};
};

int main(){

	Estructura a = {1,2};
	if( a.entero1 + a.entero2 + a.estructura3.entero5 > 0 )
		return 0;
	else
		return 1;
}
