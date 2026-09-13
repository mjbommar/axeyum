#!/usr/bin/env bash
# Run this host's share of the ADR-1946 sizing census.
# Usage: census-host.sh <shard-k...>
set -u
H=/nas3/data/axeyum/harness/dt-valued-result
export CENSUS_BIN=$H/bin/smtcomp_cli.census
OUT=$H/census-out
mkdir -p "$OUT"
BUDGET=10
pin=0
for k in "$@"; do
  cores="$pin-$((pin + 1))"
  for div in AUFDTLIRA UFDTLIRA UFDT; do
    nohup bash "$H/census-shard.sh" "$div.s$k" "$H/lists/$div.s$k.txt" \
      "$OUT/$div.s$k.tsv" "$cores" "$BUDGET" \
      >> "$OUT/$(hostname).s$k.log" 2>&1
  done &
  pin=$((pin + 2))
done
wait
echo "CENSUS-HOST-DONE $(hostname)"
