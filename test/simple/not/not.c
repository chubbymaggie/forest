/*
 * =====================================================================================
 * /
 * |     Filename:  not.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/08/2013 05:19:42 AM
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
	int a;
	int b = ~a;
	if(b == -5)
		return 0;

	if(b == 5)
		return 1;

	return 2;
}
