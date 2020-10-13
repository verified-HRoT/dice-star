#!/bin/bash

c_sum=0
for file in `ls *.c`; do
    c_sum=$(( $c_sum  +  `cat $file | wc -l`))
    echo "$file = `cat $file | wc -l`"
done

echo "Total LOC in .c: $c_sum"
echo ""
echo ""

h_sum=0
for file in `ls *.h`; do
    h_sum=$(( $h_sum  +  `cat $file | wc -l`))
    echo "$file = `cat $file | wc -l`"
done

echo "Total LOC in .h: $h_sum"
