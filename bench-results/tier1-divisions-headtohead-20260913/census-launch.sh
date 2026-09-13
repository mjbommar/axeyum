#!/usr/bin/env bash
# Launch one division's blocker census, two modulo-interleaved shards, on a box
# and a pair of physical cores given on the command line.
#
# The census is axeyum-only and runs at most one process per shard, so it can
# share a box with a board chain: measured on s5, a live solver's RSS is about
# 240 MB, and the 8 GiB `ulimit -v` is a per-run CEILING, not a reservation.
# What it must NOT share is a physical CORE with the board -- the board's
# absolute counts are the deliverable.  Pass cores no other job holds; check
# `out/loadframe.tsv`'s `foreign_cores` column first.
#
# Usage: census-launch.sh <host> <DIV> <coresA> <coresB>
#   e.g. census-launch.sh s5 AUFLIRA 1,9 7,15
set -eu
LANE="$(cd "$(dirname "$0")" && pwd)"
H=/nas3/data/axeyum/harness/tier1-divisions
HOST="$1"; DIV="$2"; CA="$3"; CB="$4"

W="$LANE/winnable/$DIV.txt"
[ -s "$W" ] || { echo "ABORT: $W missing or empty -- merge the board first"; exit 2; }
n=$(wc -l < "$W")

mkdir -p "$H/census" "$H/lists"
awk 'NR%2==1' "$W" > "$H/lists/cen.$DIV.s0"
awk 'NR%2==0' "$W" > "$H/lists/cen.$DIV.s1"
a=$(wc -l < "$H/lists/cen.$DIV.s0"); b=$(wc -l < "$H/lists/cen.$DIV.s1")
[ $((a + b)) = "$n" ] || { echo "ABORT: $DIV census shards are $a + $b of $n"; exit 2; }

ssh -o BatchMode=yes "$HOST" \
  "nohup bash -c '\"$H/census-run.sh\" \"cen.$DIV.s0\" \"$H/lists/cen.$DIV.s0\" \"$H/census/$DIV.s0.tsv\" $CA > $H/out/cen.$DIV.s0.log 2>&1 &
                  \"$H/census-run.sh\" \"cen.$DIV.s1\" \"$H/lists/cen.$DIV.s1\" \"$H/census/$DIV.s1.tsv\" $CB > $H/out/cen.$DIV.s1.log 2>&1 &
                  wait' > /dev/null 2>&1 & sleep 1; echo launched census $DIV on \$(hostname) cores $CA and $CB"
echo "census $DIV: $a + $b = $n winnable rows"
