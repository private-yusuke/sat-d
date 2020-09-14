#!/bin/bash
okcnt=0
bad=0
cnt=0
abortcnt=0
aborttime=60
for i in `find testcase -name "*.cnf"`; do
    let cnt++
    echo $i
    predict=`(timeout $aborttime ./sat-d < $i 2>/dev/null || echo ABORT) | head -n 1 | sed -e 's/s //'`
    answer=`minisat -verb=0 $i | tr -d '\n' | sed -e 's/.*precision//g'`
    
    if test "$predict" == "ABORT"; then
	    echo "abort: $i"
        let abortcnt++   
	    continue
    fi

    if test "$predict" != "$answer"; then
        echo "bad: $i"
        echo "predict: $predict"
        echo "answer: $answer"
        let bad++
        continue
    fi

    let okcnt++
done
echo "$okcnt/$cnt succeeded, $bad failed, $abortcnt aborted"
if [ $bad -ge 1 ]; then
    echo "test failed!"
	exit 1
fi
echo "test succeeded"
