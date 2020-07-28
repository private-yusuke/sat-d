#!/bin/bash
bad=0
for i in `find testcase -name "*.cnf"`; do
    echo $i
    predict=`./sat-d < $i 2>/dev/null | head -n 1 | sed -e 's/s //'`
    answer=`minisat -verb=0 $i | tr -d '\n' | sed -e 's/.*precision//g'`
    
    if test "$predict" != "$answer"; then
        echo "bad: $i"
        echo "predict: $predict"
        echo "answer: $answer"
        bad=1 
    fi
done
if [ $bad = 1 ]; then
    echo "test failed!"
	exit 1
fi
echo "test succeeded"
