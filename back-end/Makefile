
all: ../lib/forest.a ../lib/measurement.a

../lib/forest.a: ../build/database.o ../build/operators.o ../build/solver.o ../build/sqlite.o
	ar rcs ../lib/forest.a ../build/database.o ../build/operators.o ../build/solver.o ../build/sqlite.o

../build/database.o: database.cpp
	g++ -c database.cpp -o ../build/database.o

../build/operators.o: operators.cpp
	g++ -c operators.cpp -o ../build/operators.o

../build/solver.o: solver.cpp
	g++ -c solver.cpp -o ../build/solver.o

../build/sqlite.o: sqlite3.c
	gcc -c sqlite3.c -o ../build/sqlite.o

../lib/measurement.a: ../build/measurement.o ../build/database_measurement.o ../build/sqlite.o
	ar rcs ../lib/measurement.a ../build/measurement.o ../build/database_measurement.o ../build/sqlite.o

../build/measurement.o: measurement.cpp 
	g++ -c measurement.cpp -o ../build/measurement.o

../build/database_measurement.o: database_measurement.cpp
	g++ -c database_measurement.cpp -o ../build/database_measurement.o


