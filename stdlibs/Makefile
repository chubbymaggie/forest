all:
	llvm-g++ --emit-llvm -c src/getopt.c -o build/getopt.bc
	llvm-link build/getopt.bc -o lib/library.bc
