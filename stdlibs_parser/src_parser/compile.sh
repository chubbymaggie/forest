#!/bin/bash 

sed -i s/\*restrict/\*/g salida.c
lastline=`llvm-gcc salida.c --emit-llvm -c -o salida.bc 2>&1 | grep error | head -n 1`
elem=`echo $lastline | cut -d" " -f3 | sed -e s/‘//g -e s/’//g`
echo $elem
cat /tmp/ast | grep $elem
grep -Rin $elem ../musl-0.9.15/src/
opt -load /llvm-2.9/install/lib/ForestStdlibs.so -stdlibs_list_functions < salida.bc >/dev/null
