all: lib/library.bc

lib/library.bc: ../stdlibs_parser/src_parser/salida.c
	llvm-gcc --emit-llvm -c ../stdlibs_parser/src_parser/salida.c -o lib/library.bc 
	opt -load /llvm-2.9/Release+Asserts/lib/ForestStdlibs.so -stdlibs_list_functions < lib/library.bc >/dev/null
	opt -load /llvm-2.9/Release+Asserts/lib/ForestInstr.so -instr_function_names < lib/library.bc > lib/library-2.bc
	mv lib/library-2.bc lib/library.bc

clean:
	rm -rf build/*.bc lib/library-2.bc

distclean: clean
	rm -rf lib/library.bc
