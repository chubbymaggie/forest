/*
 * =====================================================================================
 * /
 * |     Filename:  getopt.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/20/2013 03:10:42 PM
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


#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>

int main(int argc, char *argv[]) {

	int flags, opt;
	int nsecs, tfnd;

	nsecs = 0;
	tfnd = 0;
	flags = 0;
	while ((opt = getopt(argc, argv, "nt:")) != -1) {
		switch (opt) {
			case 'n':
				flags = 1;
				break;
			case 't':
				nsecs = atoi(optarg);
				tfnd = 1;
				break;
			default: /* '?' */
				fprintf(stderr, "Usage: %s [-t nsecs] [-n] name\n",
						argv[0]);
				exit(EXIT_FAILURE);
		}
	}

	printf("flags=%d; tfnd=%d; optind=%d\n", flags, tfnd, optind);

	if (optind >= argc) {
		fprintf(stderr, "Expected argument after options\n");
		exit(EXIT_FAILURE);
	}

	printf("name argument = %s\n", argv[optind]);

	/* Other code omitted */

	exit(EXIT_SUCCESS);
}
