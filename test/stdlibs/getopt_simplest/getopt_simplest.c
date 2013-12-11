/*
 * =====================================================================================
 * /
 * |     Filename:  getopt-2.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/02/2013 02:19:51 PM
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

// from http://www.gnu.org/software/libc/manual/html_node/Example-of-Getopt.html

#include <stdio.h>
#include <unistd.h>

int main (int argc, char **argv) {
	int aflag = 0;
	char *cvalue = 0;
	int i = 0;
	int c;

	while ((c = getopt (argc, argv, "abc:")) != -1){
		switch (c)
		{
			case 'a':
				aflag = 1;
				break;
			case 'c':
				cvalue = optarg;
				break;
			case '?':
				fprintf (stderr, "error\n");
				return 1;
			default:
				return 0;
		}

		if(i++ == 2) break;
	}

	return 0;
}

