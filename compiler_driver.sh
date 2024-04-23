#!/bin/bash

make vcc

input_file="$1"
out_dir=$(dirname "$input_file")
out_base=$(basename "${input_file%.*}")
output_file="${out_dir}/${out_base}"

echo "$output_file"

pp_file=$(mktemp --suffix .i)
gcc -E -P "$input_file" -o "$pp_file" || { echo "preprocess failed"; exit 1; }

asm_file=$(mktemp --suffix .s)
# TODO: handle more arguments for intermediate stages (e..g --lex)
./bin/vcc "$pp_file" "$asm_file" || { echo "Compilation failed"; exit 1; }

gcc "$asm_file" -o "$output_file" || { echo "assembly failed"; exit 1; }




