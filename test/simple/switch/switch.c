/*
 * =====================================================================================
 * /
 * |     Filename:  switch.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/20/2013 04:39:48 PM
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
	switch(a){
		case 1: return 0;
		case 2: return 1;
		case 3: case 4: return 2;
	}
	return 0;
}
