/* Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
 *
 * This file is part of CREST, which is distributed under the revised
 * BSD license.  A copy of this license can be found in the file LICENSE.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
 * for details.
 */

int main(void) {

	int a;
	int b;
	int c;
	int d;

#ifdef KLEE

	klee_make_symbolic(&a, sizeof(a), "a");
	klee_make_symbolic(&b, sizeof(b), "b");
	klee_make_symbolic(&c, sizeof(c), "c");
	klee_make_symbolic(&d, sizeof(d), "d");

#endif

	if (a == 5) {
		if (b == 19) {
			if (c == 7) {
				if (d == 4) {
					return 1;
				}
			}
		}
	}

	return 0;
}
