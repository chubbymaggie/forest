.PHONY: test

all: frontend backend opt stdlibs_parser library

stdlibs_parser:
	make -C stdlibs_parser/src_parser/

library:
	make -C stdlibs

backend:
	make -C back-end

frontend:
	make -C front-end

opt:
	make -C optim-pass
clean:
	rm -rf build/*
	make -C stdlibs clean
	make -C optim-pass clean

distclean: clean
	rm -rf bin/* lib/*

test:
	@forest ./test/crest/math/config.xml                       # Simple math operations with integers
	@forest ./test/crest/simple/config.xml                     # simple operations with a variable
	@forest ./test/simple/short/config.xml                     # Short datatype
	@forest ./test/crest/uniform_test/config.xml               # nested ifs
	@forest ./test/simple/eight/config.xml                     # Eight test
	@forest ./test/crest/function/config.xml                   # function call
	@forest ./test/crest/concrete_return/config.xml            # Llamada a funciones no anotadas
	@forest ./test/simple/array/config.xml                     # Array indexing
	@forest ./test/simple/division/config.xml                  # Division
	@forest ./test/simple/fnarray/config.xml                   # Pointer passed to function
	@forest ./test/klee-examples/get_sign/config.xml           # First klee tutorial: Testing a small function
	@forest ./test/klee-examples/islower/config.xml            # First klee tutorial: Testing a small function
	@forest ./test/simple/forloop/config.xml                   # a for loop
	@forest ./test/simple/float/config.xml                     # Real operations
	@forest ./test/simple/floatint/config.xml                  # Mixing float and real operations
	@forest ./test/simple/struct/config.xml                    # Structs
	@forest ./test/simple/global/config.xml                    # global variables
	@forest ./test/simple/shift/config.xml                     # Shift operations
	@forest ./test/simple/wired_bool/config.xml                # Wired boolean operations
	@forest ./test/simple/array2d/config.xml                   # 2D array indexing
	@forest ./test/simple/array_struct/config.xml              # Array of struct
	@forest ./test/simple/array_struct_global/config.xml       # Array of global struct
	@forest ./test/simple/pointerincrement/config.xml          # incrementing a pointer
	@forest ./test/simple/force_free/config.xml                # Force a variable to be free
	@forest ./test/simple/force_free_local/config.xml          # Force a local variable to be free
	@forest ./test/simple/force_free_fn/config.xml             # Force a variable to be free with a function
	@forest ./test/simple/random_init/config.xml               # Random initialization of array
	@forest ./test/simple/forcepivot/config.xml                # Force variable pivot
	@forest ./test/simple/forcepivot_2/config.xml              # Force variable pivot 2
	@forest ./test/simple/forcepivot_global/config.xml         # Force global variable pivot
	@forest ./test/simple/forcepivot_hint/config.xml           # Force variable pivot hint
	@forest ./test/simple/force_free_and_modify/config.xml     # Force a variable to be free and modify it
	@forest ./test/simple/cmdargs/config.xml                   # command line arguments test
	@forest ./test/simple/pointernull/config.xml               # Pointer to null
	@forest ./test/simple/extern/config.xml                    # External declaration
	@forest ./test/simple/gl_pointer_init/config.xml           # Global pointer initialization
	@forest ./test/simple/gl_pointer_init_offset/config.xml    # Global pointer initialization with offset
	@forest ./test/simple/fn_pointer/config.xml                # Calling function through a pointer
	@forest ./test/simple/switch/config.xml                    # Switch statement
	@forest ./test/simple/voidfn/config.xml                    # Void function call 
	@forest ./test/simple/cmp_str_zero/config.xml              # Compare string to zero
	@forest ./test/simple/arg_constant/config.xml              # propagation of constant through function parameters
	@forest ./test/simple/align_struct/config.xml              # struct fields alignment
	@forest ./test/simple/prop_const_stack/config.xml          # Propagation of constants in the stack
	@forest ./test/simple/outofbouds/config.xml                # Access out of bounds
	@forest ./test/simple/strcmp/config.xml                    # string comparison
	@forest ./test/simple/non_annotated_twice/config.xml       # calling a system function twice
	@forest ./test/simple/andconstant/config.xml               # AND with constant
	@forest ./test/simple/orconstant/config.xml                # OR with constant
	@forest ./test/simple/not/config.xml                       # NOT operator
	@forest ./test/simple/non_annotated_n/config.xml           # Calling a non-annotated function n times
	@forest ./test/simple/and_bool/config.xml                  # ANDing two boolean variables
	@forest ./test/simple/overflow/config.xml                  # Overflow detection
	@forest ./test/simple/deref_variable/config.xml            # Dereferencing a pointer with a free variable
	@forest ./test/simple/deref_variable_store/config.xml      # Dereferencing a pointer with a free variable in store
	@forest ./test/simple/deref_variable_double/config.xml     # Double dereference with a free variable
	@forest ./test/simple/deref_variable_double_2/config.xml   # Double dereference with a free variable
	@forest ./test/simple/probem_mod/config.xml                # Avoids problematic module 0
	@forest ./test/simple/type_of_constant/config.xml          # Problem with type when assigning a constant value
	@forest ./test/simple/heuristic/config.xml                 # Heuristic
	@forest ./test/simple/array_of_strings/config.xml          # Array of Strings
	@forest ./test/simple/init_local_array/config.xml          # Initialize a local array

test_stdlib:
	@forest ./test/stdlibs/getopt/config.xml                   # getopt
	@forest ./test/stdlibs/strcpy/config.xml                   # strcpy
	@forest ./test/stdlibs/strlen/config.xml                   # strlen
	@forest ./test/stdlibs/strcat/config.xml                   # strcat
	@forest ./test/stdlibs/strcmp/config.xml                   # strcmp
	@forest ./test/stdlibs/basename/config.xml                 # basename
	@forest ./test/stdlibs/dirname/config.xml                  # dirname



test_concurrency:
	@forest ./test/concurrent/simple/config.xml
	@forest ./test/concurrent/simple2/config.xml
	@forest ./test/concurrent/simple3/config.xml
	@forest ./test/concurrent/simple4/config.xml
	@forest ./test/concurrent/simple5/config.xml
	@forest ./test/concurrent/simple6/config.xml
	@forest ./test/concurrent/simple7/config.xml


test-complex:
	@forest ./test/SNU-real-time/bs/config.xml
	@forest ./test/SNU-real-time/jfdctint/config.xml
	@forest ./test/SNU-real-time/matmul/config.xml
	@forest ./test/SNU-real-time/insertsort/config.xml
