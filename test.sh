startsec=`date +%s`
startmilisec=`date +%N`

for i in `find testcase -name "*.cnf"`; do
    predict=`./sat-d < $i | head -n 1`
    answer=`minisat -verb=0 $i | tr -d '\n' | sed -e 's/.*precision//g'`
    flag=0
    if test "$predict" != "$answer"; then
        echo "bad"
        echo "predict: $predict"
        echo "answer: $answer"
        exit 1
    fi
done

endmilisec=`date +%N`
endsec=`date +%s`
elapsedmilisec=`echo "scale=3; (${startmilisec} - ${endmilisec})/1000000000" | bc`
elapsedsec=`expr ${endsec} - ${startsec}`
echo "$elapsedsec$elapsedmilisec seconds"
if [ $flag = 0 ]; then
    echo "ok"
fi