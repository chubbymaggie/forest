CXX = g++
CFLAGS = -fno-rtti

LLVM_SRC_PATH = /llvm-3.3
LLVM_BUILD_PATH = /llvm-3.3

LLVM_BIN_PATH = $(LLVM_BUILD_PATH)/Debug+Asserts/bin
LLVM_LIBS=core mc
LLVM_CONFIG_COMMAND = $(LLVM_BIN_PATH)/llvm-config --cxxflags --ldflags \
		      --libs $(LLVM_LIBS)
LLVM_CONFIG_COMMAND_RESULT = -I/llvm-3.3/include -I/llvm-3.3/include  -D_DEBUG -D_GNU_SOURCE -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -O3 -fomit-frame-pointer -fvisibility-inlines-hidden -fno-exceptions -fno-rtti -fPIC -Woverloaded-virtual -Wcast-qual -L/llvm-3.3/Release+Asserts/lib  -lpthread -lrt -ldl -lm -lLLVMMC -lLLVMObject -lLLVMCore -lLLVMSupport

LLVM_CONFIG_LIBS = -lLLVMInstrumentation -lLLVMArchive -lLLVMLinker -lLLVMIRReader -lLLVMBitReader -lLLVMAsmParser -lLLVMDebugInfo -lLLVMOption -lLLVMipo -lLLVMVectorize -lLLVMBitWriter -lLLVMTableGen -lLLVMSystemZCodeGen -lLLVMSystemZAsmParser -lLLVMSystemZDesc -lLLVMSystemZInfo -lLLVMSystemZAsmPrinter -lLLVMHexagonCodeGen -lLLVMHexagonAsmPrinter -lLLVMHexagonDesc -lLLVMHexagonInfo -lLLVMNVPTXCodeGen -lLLVMNVPTXDesc -lLLVMNVPTXInfo -lLLVMNVPTXAsmPrinter -lLLVMMBlazeDisassembler -lLLVMMBlazeCodeGen -lLLVMMBlazeDesc -lLLVMMBlazeAsmPrinter -lLLVMMBlazeAsmParser -lLLVMMBlazeInfo -lLLVMCppBackendCodeGen -lLLVMCppBackendInfo -lLLVMMSP430CodeGen -lLLVMMSP430Desc -lLLVMMSP430Info -lLLVMMSP430AsmPrinter -lLLVMXCoreDisassembler -lLLVMXCoreCodeGen -lLLVMXCoreDesc -lLLVMXCoreInfo -lLLVMXCoreAsmPrinter -lLLVMMipsDisassembler -lLLVMMipsCodeGen -lLLVMMipsAsmParser -lLLVMMipsDesc -lLLVMMipsInfo -lLLVMMipsAsmPrinter -lLLVMARMDisassembler -lLLVMARMCodeGen -lLLVMARMAsmParser -lLLVMARMDesc -lLLVMARMInfo -lLLVMARMAsmPrinter -lLLVMAArch64Disassembler -lLLVMAArch64CodeGen -lLLVMAArch64AsmParser -lLLVMAArch64Desc -lLLVMAArch64Info -lLLVMAArch64AsmPrinter -lLLVMAArch64Utils -lLLVMPowerPCCodeGen -lLLVMPowerPCDesc -lLLVMPowerPCAsmPrinter -lLLVMPowerPCAsmParser -lLLVMPowerPCInfo -lLLVMSparcCodeGen -lLLVMSparcDesc -lLLVMSparcInfo -lLLVMX86Disassembler -lLLVMX86AsmParser -lLLVMX86CodeGen -lLLVMSelectionDAG -lLLVMAsmPrinter -lLLVMX86Desc -lLLVMX86Info -lLLVMX86AsmPrinter -lLLVMX86Utils -lgtest_main -lgtest -lLLVMMCDisassembler -lLLVMMCParser -lLLVMInterpreter -lLLVMMCJIT -lLLVMJIT -lLLVMCodeGen -lLLVMObjCARCOpts -lLLVMScalarOpts -lLLVMInstCombine -lLLVMTransformUtils -lLLVMipa -lLLVMAnalysis -lLLVMRuntimeDyld -lLLVMExecutionEngine -lLLVMTarget -lLLVMMC -lLLVMObject -lLLVMCore -lLLVMSupport


CLANG_BUILD_FLAGS = -I$(LLVM_SRC_PATH)/tools/clang/include \
		    -I$(LLVM_BUILD_PATH)/tools/clang/include \
		    -I$(LLVM_BUILD_PATH)/include

#CLANGLIBS = \
	    #-lclangFrontendTool -lclangFrontend -lclangDriver \
	    #-lclangSerialization -lclangCodeGen -lclangParse \
	    #-lclangSema -lclangStaticAnalyzerFrontend \
	    #-lclangStaticAnalyzerCheckers -lclangStaticAnalyzerCore \
	    #-lclangAnalysis -lclangARCMigrate -lclangRewriteCore -lclangRewriteFrontend \
	    #-lclangEdit -lclangAST -lclangLex -lclangBasic \
	    #-ldl

CLANGLIBS = \
				-lclangTooling\
				-lclangFrontendTool\
				-lclangFrontend\
				-lclangDriver\
				-lclangSerialization\
				-lclangCodeGen\
				-lclangParse\
				-lclangSema\
				-lclangStaticAnalyzerFrontend\
				-lclangStaticAnalyzerCheckers\
				-lclangStaticAnalyzerCore\
				-lclangAnalysis\
				-lclangARCMigrate\
				-lclangRewriteFrontend\
				-lclangRewriteCore\
				-lclangEdit\
				-lclangAST\
				-lclangLex\
				-lclangBasic\
				$(LLVM_CONFIG_LIBS) \
				-lncurses -ldl -lpthread

all: rewritersample

rewritersample: rewritersample.cpp
	$(CXX) stdlibs_parser.cpp -o stdlibs_parser \
		$(CFLAGS) $(LLVM_CONFIG_COMMAND_RESULT) $(CLANG_BUILD_FLAGS) $(CLANGLIBS)
clean:
	rm -rf *.o *.ll stdlibs_parser
