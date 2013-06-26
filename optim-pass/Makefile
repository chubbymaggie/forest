all: /llvm-2.9/install/lib/ForestInstr.so /llvm-2.9/install/lib/ForestMeasure.so

/llvm-2.9/install/lib/ForestInstr.so: instrumentation_pass.cpp 
	sudo mkdir -p /llvm-2.9/lib/Transforms/Forest_instr/
	sudo touch /llvm-2.9/lib/Transforms/Forest_instr/Forest_instr.exports
	sudo cp make_instr /llvm-2.9/lib/Transforms/Forest_instr/Makefile
	sudo cp instrumentation_pass.cpp /llvm-2.9/lib/Transforms/Forest_instr/forest_instr.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_instr/; sudo make;
	cd /llvm-2.9/lib/Transforms/Forest_instr/; sudo make install;

/llvm-2.9/install/lib/ForestMeasure.so: measurement_pass.cpp
	sudo mkdir -p /llvm-2.9/lib/Transforms/Forest_measure/
	sudo touch /llvm-2.9/lib/Transforms/Forest_measure/Forest_measure.exports
	sudo cp make_measure /llvm-2.9/lib/Transforms/Forest_measure/Makefile
	sudo cp measurement_pass.cpp /llvm-2.9/lib/Transforms/Forest_measure/Forest_measure.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_measure/; sudo make;
	cd /llvm-2.9/lib/Transforms/Forest_measure/; sudo make install;

clean:
	sudo rm -rf /llvm-2.9/install/lib/ForestInstr.so
	sudo rm -rf /llvm-2.9/install/lib/ForestMeasure.so
