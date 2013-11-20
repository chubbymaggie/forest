all:
	llvm-gcc --emit-llvm -c src/long_options.c -o build/long_options.bc
	llvm-link build/long_options.bc -o lib/library.bc
