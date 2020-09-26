#!/bin/bash
okcnt=0
bad=0
cnt=0
abortcnt=0
aborttime=60
for i in `find testcase -name "*.cnf"`; do
    let cnt++
    echo $i
    _predict=`timeout $aborttime ./sat-d < $i 2>/dev/null`
    status=$?
    if [ $status -eq 124 ]; then
        predict="ABORT"
    elif [ $status -eq 0 ]; then
        predict=`echo $_predict | head -n 1 | sed -e 's/s //'`
    else
        predict="ERROR"
    fi
    answer=`minisat -verb=0 $i | tr -d '\n' | sed -e 's/.*precision//g'`
    
    if test "$predict" == "ABORT"; then
	    echo "abort: $i"
        let abortcnt++   
	    continue
    fi

    if test "$predict" == "ERROR"; then
        echo "abort the entire run because an error occured while runnng sat-d"
        exit 2
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
