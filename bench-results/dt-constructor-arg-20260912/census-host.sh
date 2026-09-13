#!/usr/bin/env bash
set -u
H=/nas3/data/axeyum/harness/dt-constructor-arg
export CENSUS_BIN=$H/bin/smtcomp_cli.census2
OUT=$H/census2-out
mkdir -p "$OUT"
BUDGET=10
pin=0
for k in "$@"; do
  cores="$pin-$((pin + 1))"
  for div in AUFDTLIRA UFDTLIRA UFDT; do
    nohup bash "$H/census-shard2.sh" "$div.s$k" "$H/lists/$div.s$k.txt" \
      "$OUT/$div.s$k.tsv" "$cores" "$BUDGET" \
      >> "$OUT/$(hostname).s$k.log" 2>&1
  done &
  pin=$((pin + 2))
done
wait
echo "CENSUS2-HOST-DONE $(hostname)"
