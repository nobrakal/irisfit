#!/bin/bash

count_lines () {
    num=0
    for line in $(find $1 -type f -name "*.v" -printf '%p\n' )
    do
	spec=$(coqwc -s $line | awk '{print $1;}')
	proof=$(coqwc -r $line | awk '{print $1;}')
	num=$(($num + $spec + $proof))
    done
    echo $num
}

echo "Number of lines as counted by coqwc, excluding comments. "
echo -n "Language, core: "
count_lines "src/language"

echo -n "Language, final: "
count_lines "src/final"

echo -n "Logic: "
count_lines "src/program_logic"

echo -n "Examples: "
count_lines "src/examples"

echo -n "Preexisting libraries: "
count_lines "src/lib src/spacelang"
