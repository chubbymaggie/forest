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


int getopt(int, char* const*, char const*);

int main () {

	int argc = 2;
	char* argv[] = {"ab", "cd"};

	int c = getopt (argc, argv, "ac:");

	switch (c)
	{
		case 'a':
			break;
		case 'c':
			break;
		case '?':
			return 1;
		default:
			return 0;
	}

	return 0;
}

