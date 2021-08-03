#!/bin/bash

cnt=0
bad=0
mode="randkcnf"
args="1 5 10"
git_latest=$(git log --oneline | head -n 1 | cut -d' ' -f 1)
while [ $bad -lt 10 ]
do
	cnt=$((cnt+1))
	echo $cnt
	name="bad$bad-$git_latest-$mode-$(echo "$args" | sed -e 's/\s/-/g').cnf"
	cnfgen $mode $args > $name
	cl=$(clasp $name | grep -G "^s")
	sd=$(./sat-d-demo < $name | grep -G "^s")
	if [ "$cl" != "$sd" ]
	then
		bad=$((bad+1))
		echo "cnt: $cnt, bad: $bad"
		echo "cl=$cl"
		echo "sd=$sd"
		
	fi
done

