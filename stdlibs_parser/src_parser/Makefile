all: stdlibs_parser extract_library compile_extracted

stdlibs_parser: stdlibs_parser.cpp
	g++ -g stdlibs_parser.cpp -o stdlibs_parser 

extract_library:
	./stdlibs_parser > salida.c

compile_extracted:
	./compile.sh

clean:
	rm -rf *.o *.ll stdlibs_parser
