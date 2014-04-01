
all: ../lib/forest.a 

../lib/forest.a: ../build/database.o ../build/operators.o ../build/solver_wrapper.o ../build/z3_solver.o ../build/sqlite.o ../build/utils.o ../build/options.o ../build/wrapper.o ../build/concurrency.o ../build/measurement.o ../build/timer.o
	ar rcs ../lib/forest.a ../build/database.o ../build/operators.o ../build/solver_wrapper.o ../build/z3_solver.o ../build/sqlite.o ../build/utils.o ../build/options.o ../build/wrapper.o ../build/concurrency.o ../build/measurement.o ../build/timer.o

../build/wrapper.o: wrapper.cpp
	g++ -g -c wrapper.cpp -o ../build/wrapper.o

../build/options.o: options.cpp
	g++ -g -c options.cpp -o ../build/options.o

../build/utils.o: utils.cpp 
	g++ -g -c utils.cpp -o ../build/utils.o

../build/database.o: database.cpp
	g++ -g -c database.cpp -o ../build/database.o

../build/operators.o: operators.cpp
	g++ -g -c operators.cpp -o ../build/operators.o

../build/solver_wrapper.o: solver_wrapper.cpp
	g++ -g -c solver_wrapper.cpp -o ../build/solver_wrapper.o

../build/z3_solver.o: z3_solver.cpp
	g++ -g -c z3_solver.cpp -o ../build/z3_solver.o

../build/sqlite.o: sqlite3.c
	gcc -g -c sqlite3.c -o ../build/sqlite.o

../build/measurement.o: measurement.cpp 
	g++ -g -c measurement.cpp -o ../build/measurement.o

../build/concurrency.o: concurrency.cpp 
	g++ -g -c concurrency.cpp -o ../build/concurrency.o 

../build/timer.o: timer.cpp 
	g++ -g -c timer.cpp -o ../build/timer.o 

