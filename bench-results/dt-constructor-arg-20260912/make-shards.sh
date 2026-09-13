#!/usr/bin/env bash
set -eu
H=/nas3/data/axeyum/harness/dt-constructor-arg
D=$H/lists
for div in AUFDTLIRA UFDTLIRA UFDT QF_DT UF; do
  for k in $(seq 0 11); do
    awk -v k="$k" 'NR%12==k' "$D/$div.full.txt" > "$D/$div.s$k.txt"
  done
done
wc -l "$D"/*.s*.txt | tail -1
