#!/usr/bin/env bash
# Master driver for the QF_NIA Groebner-gate ladder: 16, 32, 64, unbounded,
# each interleaved shipped-vs-gateN over the 116 undecided rows, two shards
# (cores 1,9 and 3,11) in parallel, divisions serial per shard.
set -u
HERE=/home/mjbommar/nia-groebner-gate-20260915
LIST=$HERE/lists/undecided-116.txt
SHARD1=$HERE/lists/undecided-116-shard1.txt
SHARD2=$HERE/lists/undecided-116-shard2.txt

awk 'NR % 2 == 1' "$LIST" > "$SHARD1"
awk 'NR % 2 == 0' "$LIST" > "$SHARD2"
echo "shard1: $(wc -l < "$SHARD1") files, shard2: $(wc -l < "$SHARD2") files"

for rung in "16" "32" "64" "unbounded"; do
  lever="$rung"
  [ "$rung" = "unbounded" ] && lever=1000000
  echo "=== rung $rung (lever=$lever) starting $(date -Is) ==="
  "$HERE/scripts/run-arm-pair.sh" "$rung" "$lever" "$SHARD1" "1,9" "$rung" &
  p1=$!
  "$HERE/scripts/run-arm-pair.sh" "$rung" "$lever" "$SHARD2" "3,11" "$rung" &
  p2=$!
  wait "$p1"; rc1=$?
  wait "$p2"; rc2=$?
  echo "=== rung $rung done $(date -Is) rc1=$rc1 rc2=$rc2 ==="
done
echo "LADDER-MASTER-DONE $(date -Is)"
