#!/bin/bash
bad=0
cnt=0
for benchdir in `cat benchmark_dir.txt`; do
	for i in `find $benchdir -name "*.cnf"`; do
	    echo `basename $i`,`./sat-d benchmark < $i 2>/dev/null`
	done
done
