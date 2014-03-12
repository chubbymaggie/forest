#!/bin/bash 


list=`find /llvm-2.9/klee-uclibc-0.02-x64/ | xargs file | grep 'LLVM bitcode' | cut -d":" -f1`
dirlist=$(for a in $list; do dirname `echo $a | sed 's/\/llvm-2.9\/klee-uclibc-0.02-x64\///g'` ; done | sort | uniq)
for a in $dirlist; do mkdir -p $a; done
for a in $list; do echo cp $a " " `echo $a | sed 's/\/llvm-2.9\/klee-uclibc-0.02-x64\///g'`; done | bash

os=`find -type f | grep -v get_klee_uclib.sh`
for a in $os; do opt -strip < $a > $a.2; done
for a in $os; do mv $a.2 $a; done


