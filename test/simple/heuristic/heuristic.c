/*
 * =====================================================================================
 * /
 * |     Filename:  heuristic.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  01/24/2014 04:02:09 PM
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


int funcion(){

	int a;
	int i = 3;
	for(a = 0; a < i; a++){}

	if(a == 3)
		return 0;   // (A)
	else
		return 1;
}

int main() {


	int j;
	int k;
	int* l;

	if(j){
		funcion();
	}

	if(k){
		
	} else {
		funcion();
	}

	if(*l){
		funcion();
	}

}

