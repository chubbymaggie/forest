#!/bin/bash 

llvm-g++ getenv.c -c --emit-llvm
llvm-gcc environ.c -c --emit-llvm
llvm-link getenv.o environ.o -o getenv.bc
