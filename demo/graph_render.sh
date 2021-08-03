#!/bin/sh
find . -name "*.dot" | xargs -P 16 -I {} dot -Tpng {} -o {}.png