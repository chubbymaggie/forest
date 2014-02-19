all: /llvm-2.9/install/lib/ForestInstr.so /llvm-2.9/install/lib/ForestMeasure.so /llvm-2.9/install/lib/ForestConcurrency.so /llvm-2.9/install/lib/ForestStdlibs.so /llvm-2.9/install/lib/ForestHeuristic.so

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

/llvm-2.9/install/lib/ForestConcurrency.so: concurrency_pass.cpp
	sudo mkdir -p /llvm-2.9/lib/Transforms/Forest_concurrency/
	sudo touch /llvm-2.9/lib/Transforms/Forest_concurrency/Forest_concurrency.exports
	sudo cp make_concurrency /llvm-2.9/lib/Transforms/Forest_concurrency/Makefile
	sudo cp concurrency_pass.cpp /llvm-2.9/lib/Transforms/Forest_concurrency/Forest_concurrency.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_concurrency/; sudo make;
	cd /llvm-2.9/lib/Transforms/Forest_concurrency/; sudo make install;

/llvm-2.9/install/lib/ForestStdlibs.so: stdlibs_pass.cpp
	sudo mkdir -p /llvm-2.9/lib/Transforms/Forest_stdlibs/
	sudo touch /llvm-2.9/lib/Transforms/Forest_stdlibs/Forest_stdlibs.exports
	sudo cp make_stdlibs /llvm-2.9/lib/Transforms/Forest_stdlibs/Makefile
	sudo cp stdlibs_pass.cpp /llvm-2.9/lib/Transforms/Forest_stdlibs/Forest_stdlibs.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_stdlibs/; sudo make;
	cd /llvm-2.9/lib/Transforms/Forest_stdlibs/; sudo make install;

/llvm-2.9/install/lib/ForestHeuristic.so: heuristic_pass.cpp
	sudo mkdir -p /llvm-2.9/lib/Transforms/Forest_heuristic/
	sudo touch /llvm-2.9/lib/Transforms/Forest_heuristic/Forest_heuristic.exports
	sudo cp make_heuristic /llvm-2.9/lib/Transforms/Forest_heuristic/Makefile
	sudo cp heuristic_pass.cpp                 /llvm-2.9/lib/Transforms/Forest_heuristic/Forest_heuristic.cpp 
	sudo cp graph/DijkstraShortestPathAlg.cpp  /llvm-2.9/lib/Transforms/Forest_heuristic/
	sudo cp graph/DijkstraShortestPathAlg.h    /llvm-2.9/lib/Transforms/Forest_heuristic/
	sudo cp graph/Graph.cpp                    /llvm-2.9/lib/Transforms/Forest_heuristic/
	sudo cp graph/Graph.h                      /llvm-2.9/lib/Transforms/Forest_heuristic/
	sudo cp graph/GraphElements.h              /llvm-2.9/lib/Transforms/Forest_heuristic/
	sudo cp graph/YenTopKShortestPathsAlg.cpp  /llvm-2.9/lib/Transforms/Forest_heuristic/
	sudo cp graph/YenTopKShortestPathsAlg.h    /llvm-2.9/lib/Transforms/Forest_heuristic/
	cd /llvm-2.9/lib/Transforms/Forest_heuristic/; sudo make;
	cd /llvm-2.9/lib/Transforms/Forest_heuristic/; sudo make install;

clean:
	sudo rm -rf /llvm-2.9/install/lib/ForestInstr.so
	sudo rm -rf /llvm-2.9/install/lib/ForestMeasure.so
	sudo rm -rf /llvm-2.9/install/lib/ForestConcurrency.so
	sudo rm -rf /llvm-2.9/install/lib/ForestStdlibs.so
