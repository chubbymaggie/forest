.PHONY: final 


bc:
	sudo cp optimization_pass.cpp /llvm-2.9/lib/Transforms/Hello/Hello.cpp # copiar el paso a la carpeta
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make; # make del paso de optimización
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make install; # make install del paso de optimización 
	llvm-gcc -O0 --emit-llvm -c get-sign.cpp -o get-sign.bc # compilación del código a bc
	opt -load /llvm-2.9/Release+Asserts/lib/LLVMHello.so -fill_names < get-sign.bc > get-sign-2.bc # primer paso de optimización 
	llvm-dis < get-sign-2.bc > salida1.txt # generar salida1 
	opt -load /llvm-2.9/Release+Asserts/lib/LLVMHello.so -getelementptr < get-sign-2.bc > get-sign-3.bc # segundo paso de optimización --------
	llvm-dis < get-sign-3.bc > salida2.txt # generar salida2 

compare:
	sudo cp optimization_pass.cpp /llvm-2.9/lib/Transforms/Hello/Hello.cpp # copiar el paso a la carpeta
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make; # make del paso de optimización
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make install; # make install del paso de optimización 
	llvm-gcc -O0 --emit-llvm -c get-sign.cpp -o get-sign.bc # compilación del código a bc
	opt -load /llvm-2.9/Release+Asserts/lib/LLVMHello.so -fill_names < get-sign.bc > get-sign-2.bc # primer paso de optimización 
	llvm-dis < get-sign-2.bc > salida1.txt # generar salida1 
	opt -load /llvm-2.9/Release+Asserts/lib/LLVMHello.so -getelementptr < get-sign-2.bc > get-sign-3.bc # segundo paso de optimización --------
	llvm-dis < get-sign-3.bc > salida2.txt # generar salida2 
	meld salida1.txt salida2.txt # comparar salida1 y salida2

viewbc:
	sudo cp optimization_pass.cpp /llvm-2.9/lib/Transforms/Hello/Hello.cpp # copiar el paso a la carpeta
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make; # make del paso de optimización
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make install; # make install del paso de optimización 
	llvm-gcc -O0 --emit-llvm -c get-sign.cpp -o get-sign.bc # compilación del código a bc
	opt -load /llvm-2.9/Release+Asserts/lib/LLVMHello.so -fill_names < get-sign.bc > get-sign-2.bc # primer paso de optimización 
	llvm-dis < get-sign-2.bc > salida1.txt # generar salida1 
	gedit salida1.txt

final:
	llc get-sign-3.bc -o get-sign-3.s
	gcc -c get-sign-3.s -o get-sign-3.o
	g++ -g -c operators.cpp  -o operators.o
	g++ -g -c solver.cpp -o solver.o
	gcc -c sqlite3.c -o sqlite3.o
	g++ -c database.cpp -o database.o
	g++ get-sign-3.o operators.o solver.o sqlite3.o database.o -lboost_regex -lpthread -ldl -o final

run:
	rm -rf /tmp/z3_*
	./final


all:
	g++ -D TEST get-sign.cpp

clean:
	rm -rf forest *.out *.bc salida* *.o *.s final test.cpp database.db


llvm-dfg:
	sudo cp optimization_pass.cpp /llvm-2.9/lib/Transforms/Hello/Hello.cpp
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make;
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make install;
	llvm-gcc --emit-llvm -c get-sign.cpp -o get-sign.bc
	opt -dot-cfg < get-sign.bc
	dot -T png cfg._Z8get_booli.dot > salida1.png
	opt -load /llvm-2.9/Release+Asserts/lib/LLVMHello.so -v_instrument < get-sign.bc > get-sign-2.bc
	opt -dot-cfg < get-sign-2.bc
	dot -T png cfg._Z8get_booli.dot > salida2.png 
	eog salida1.png & eog salida2.png &


test:
	llvm-gcc -O0 --emit-llvm -c test.c -o test.bc
	llvm-dis < test.bc > salida-test.txt
	gedit salida-test.txt

testopt:
	llvm-gcc -O3 --emit-llvm -c test.c -o test.bc
	llvm-dis < test.bc > salida-test.txt
	gedit salida-test.txt

untest:
	llc -march=cpp test.bc
	gedit test.cpp

