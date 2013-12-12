all: lib/library.bc

build/getopt.bc: src/getopt.c 
	llvm-g++ --emit-llvm -c src/getopt.c -o build/getopt.bc

build/string.bc: src/string.c
	llvm-g++ --emit-llvm -c src/string.c -o build/string.bc

lib/library.bc: build/getopt.bc build/string.bc
	llvm-link build/getopt.bc build/string.bc -o lib/library.bc 
	opt -load /llvm-2.9/Release+Asserts/lib/ForestStdlibs.so -stdlibs_list_functions < lib/library.bc >/dev/null
	opt -load /llvm-2.9/Release+Asserts/lib/ForestInstr.so -instr_function_names < lib/library.bc > lib/library-2.bc
	mv lib/library-2.bc lib/library.bc

clean:
	rm -rf list build/*.bc
