#!/usr/bin/env bash
# Split each pinned 200-file list into 12 modulo-interleaved shards, so every
# shard spans the whole division rather than a path-sorted prefix of one author
# directory. Shard k gets lines with NR%12 == k.
set -eu
D=/nas3/data/axeyum/harness/dt-capability/lists
for div in AUFDTLIRA UFDTLIRA UFDT QF_DT UF; do
  for k in $(seq 0 11); do
    awk -v k="$k" 'NR%12==k' "$D/$div.full.txt" > "$D/$div.s$k.txt"
  done
done
wc -l "$D"/*.s*.txt | tail -1
