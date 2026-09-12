#!/usr/bin/env bash
# Run this host's share of the ADR-1935 A/B: four shards, each on its own pinned
# core pair, each running both arms back to back per file.
#
# Usage: run-host.sh <shard-k-list...>   e.g. run-host.sh 0 1 2 3
set -u
H=/nas3/data/axeyum/harness/dt-capability
export AB_BASE=$H/bin/smtcomp_cli.base
export AB_NEW=$H/bin/smtcomp_cli.new
OUT=$H/out
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
echo "HOST-DONE $(hostname)"
