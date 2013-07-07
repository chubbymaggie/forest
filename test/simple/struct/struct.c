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


typedef struct Estructura {
	int entero1;
} Estructura;

int main(){

	Estructura a;
	if( a.entero1 > 0 )
		return 0;
	else
		return 1;
}
