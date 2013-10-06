/*
 * =====================================================================================
 * /
 * |     Filename:  force_free_fn.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/06/2013 03:06:42 AM
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

void force_free(int* a);

int main() {
	
	int a = 5;
	force_free(&a);
	if(a == 5)
		return 0;
	else
		return 1;
}
