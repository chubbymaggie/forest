all:
	llvm-g++ --emit-llvm -c src/getopt.c -o build/getopt.bc
	llvm-g++ --emit-llvm -c src/string.c -o build/string.bc
	llvm-link build/getopt.bc build/string.bc -o lib/library.bc
