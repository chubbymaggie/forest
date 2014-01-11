all: ../bin/forest

../bin/forest: ../build/forest.o ../build/tinystr.o ../build/tinyxml.o ../build/tinyxmlerror.o ../build/tinyxmlparser.o 
	g++ ../build/forest.o ../build/tiny*.o -o ../bin/forest -lrt

../build/forest.o: forest.cpp 
	g++ -g -c forest.cpp -o ../build/forest.o

../build/tinystr.o: tinystr.cpp 
	g++ -c tinystr.cpp -o ../build/tinystr.o

../build/tinyxml.o: tinyxml.cpp 
	g++ -c tinyxml.cpp -o ../build/tinyxml.o

../build/tinyxmlerror.o: tinyxmlerror.cpp 
	g++ -c tinyxmlerror.cpp -o ../build/tinyxmlerror.o


../build/tinyxmlparser.o: tinyxmlparser.cpp 
	g++ -c tinyxmlparser.cpp -o ../build/tinyxmlparser.o



