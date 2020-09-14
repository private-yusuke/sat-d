#!/bin/bash
bad=0
cnt=0
aborttime=60
for benchdir in `cat benchmark_dir.txt`; do
	for i in `find $benchdir -name "*.cnf"`; do
	    echo `basename $i`,`timeout $aborttime ./sat-d benchmark < $i 2>/dev/null || echo "ABORT,-1"`
	done
done
