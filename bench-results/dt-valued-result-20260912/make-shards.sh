#!/usr/bin/env bash
# Twelve modulo-interleaved shards per division. Interleaved rather than
# contiguous because the parity lists are PATH-sorted, so a contiguous split
# gives each shard one benchmark family and the shards finish at wildly
# different times.
set -eu
H=/nas3/data/axeyum/harness/dt-valued-result
D=$H/lists
for div in AUFDTLIRA UFDTLIRA UFDT QF_DT UF; do
  for k in $(seq 0 11); do
    awk -v k="$k" 'NR%12==k' "$D/$div.full.txt" > "$D/$div.s$k.txt"
  done
done
wc -l "$D"/*.s*.txt | tail -1
