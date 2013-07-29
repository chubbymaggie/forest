/*
 * =====================================================================================
 * /
 * |     Filename:  pointerincrement.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/26/2013 10:52:46 AM
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


int main() {

	static float variable[5] = {1.0, 2.0, 3.0, 4.0, 5.0};

	float* pointer = variable;

	/*for ( unsigned int i = 0; i < 10; i++)*/
		pointer++;

	if( *pointer == 2.0 )
		return 0;
	else
		return 1;
}
