#!/bin/bash
for i in `find testcase -name "*.cnf"`; do
    predict=`./sat-d < $i | head -n 1 | sed -e 's/s //'`
    answer=`minisat -verb=0 $i | tr -d '\n' | sed -e 's/.*precision//g'`
    
    if test "$predict" != "$answer"; then
        echo "bad"
        echo "predict: $predict"
        echo "answer: $answer"
        exit 1
    fi
done
echo "ok"