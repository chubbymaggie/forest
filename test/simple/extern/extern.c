/*
 * =====================================================================================
 * /
 * |     Filename:  extern.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/14/2013 11:05:28 AM
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

int b;
extern int a;

int main() {
	if(a)
		return 0;
	else
		return 1;
}
