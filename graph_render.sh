#!/bin/sh
for i in $(find . -name "*.dot")
do
    dot -Tpng $i -o $i.png
done