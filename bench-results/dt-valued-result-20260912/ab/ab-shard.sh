#!/usr/bin/env bash
# One shard of the ADR-1935 A/B: two axeyum binaries on the same file, back to
# back on the same pinned core pair, alternating which arm goes first.
#
# FAIRNESS: both arms finish file N before either starts N+1, so ambient drift
# on the box cancels in the difference.  The arm that goes first alternates per
# file so neither systematically benefits from a cold or warm page cache.
#
# The wrapper timeout is BUDGET + HEADROOM and every run records its own
# outcome, because a previous census used a short headroom under load, killed
# processes, and produced rows that read as "no reason".
#
# Usage: ab-shard.sh <tag> <list> <out.tsv> <cores> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-10}"
HEADROOM=16
BASE="${AB_BASE:?set AB_BASE to the baseline smtcomp_cli}"
NEW="${AB_NEW:?set AB_NEW to the candidate smtcomp_cli}"
for b in "$BASE" "$NEW"; do
  [ -x "$b" ] || { echo "ABORT $TAG: $b missing or not executable"; exit 2; }
done
VLIM=$((8 * 1024 * 1024))   # ulimit -v is KiB -> 8 GiB, the board protocol

run() { # $1 binary  $2 file -> "verdict<TAB>seconds<TAB>giveup"
  local t0 t1 raw rc v g
  t0=$(date +%s.%N)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000)) --trace" \
          "$1" "$2" 2>&1)
  rc=$?
  t1=$(date +%s.%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat)$')
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | cut -c1-200)
  [ "$rc" = 124 ] && g="WRAPPER-KILLED"
  [ "$rc" = 134 ] && g="RC134-ABORT"
  [ "$rc" = 137 ] && g="SIGKILL"
  printf '%s\t%s\t%s' "${v:-unknown}" \
    "$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.2f", b-a}')" \
    "${g:-none}"
}

printf 'file\tbase\tbase_s\tbase_giveup\tnew\tnew_s\tnew_giveup\tstatus\n' > "$OUT"
i=0
while read -r f; do
  [ -n "$f" ] || continue
  i=$((i + 1))
  if [ $((i % 2)) = 0 ]; then b=$(run "$BASE" "$f"); n=$(run "$NEW" "$f")
  else                        n=$(run "$NEW" "$f");  b=$(run "$BASE" "$f"); fi
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' "$f" | awk '{print $2}')
  printf '%s\t%s\t%s\t%s\n' "$f" "$b" "$n" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
