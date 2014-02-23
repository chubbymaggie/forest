all: stdlibs_parser extract_library compile_extracted

stdlibs_parser: stdlibs_parser.cpp
	g++ -g stdlibs_parser.cpp -o stdlibs_parser 

extract_library:
	./stdlibs_parser > salida.cpp

compile_extracted:
	llvm-g++ salida.cpp --emit-llvm -c -o salida.bc
	opt -load /llvm-2.9/install/lib/ForestStdlibs.so -stdlibs_list_functions < salida.bc >/dev/null

clean:
	rm -rf *.o *.ll stdlibs_parser
