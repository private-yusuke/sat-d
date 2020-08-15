#!/bin/bash
bad=0
cnt=0
for i in `find testcase -name "*.cnf"`; do
    echo `basename $i`,`./sat-d benchmark < $i 2>/dev/null`
done