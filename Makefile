.PHONY: final test


backend:
	g++ -c back-end/database.cpp -o build/database.o
	g++ -c back-end/operators.cpp -o build/operators.o
	g++ -c back-end/solver.cpp -o build/solver.o
	gcc -c back-end/sqlite3.c -o build/sqlite.o
	ar rcs lib/forest.a build/database.o build/operators.o build/solver.o build/sqlite.o

frontend:
	g++ -c -g front-end/forest.cpp -o build/forest.o
	g++ -c front-end/tinystr.cpp  -o build/tinystr.o
	g++ -c front-end/tinyxml.cpp  -o build/tinyxml.o
	g++ -c front-end/tinyxmlerror.cpp  -o build/tinyxmlerror.o
	g++ -c front-end/tinyxmlparser.cpp  -o build/tinyxmlparser.o
	g++ build/forest.o build/tiny*.o -o bin/forest
	
clean:
	rm -rf build/*

distclean: clean
	rm -rf bin/*

test:
	@forest ./test/crest/math/config.xml
	@forest ./test/crest/simple/config.xml
	@forest ./test/crest/uniform_test/config.xml
	@forest ./test/crest/function/config.xml

