all: stdlibs_parser extract_library

stdlibs_parser: stdlibs_parser.cpp
	g++ -g stdlibs_parser.cpp -o stdlibs_parser 

extract_library:
	./stdlibs_parser > salida.cpp

clean:
	rm -rf *.o *.ll stdlibs_parser
