#!/usr/bin/env bash
# Run this host's share of the ADR-1942 A/B: four shards, each on its own pinned
# core pair, each running both arms back to back per file.
#
# Usage: ab-host.sh <shard-k...>
set -u
H=/nas3/data/axeyum/harness/dt-constructor-arg
export AB_BASE=$H/bin/smtcomp_cli.base
export AB_NEW=$H/bin/smtcomp_cli.new
OUT=$H/ab-out
mkdir -p "$OUT"
BUDGET=10
pin=0
for k in "$@"; do
  cores="$pin-$((pin + 1))"
  for div in AUFDTLIRA UFDTLIRA UFDT QF_DT UF; do
    nohup bash "$H/ab-shard.sh" "$div.s$k" "$H/lists/$div.s$k.txt" \
      "$OUT/$div.s$k.tsv" "$cores" "$BUDGET" \
      >> "$OUT/$(hostname).s$k.log" 2>&1
  done &
  pin=$((pin + 2))
done
wait
echo "AB-HOST-DONE $(hostname)"
