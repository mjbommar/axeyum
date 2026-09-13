#!/usr/bin/env bash
# One shard of the ADR-1946 SIZING census. Dumps RAW records and leaves all
# aggregation to Python, so a change to the census fields does not need a change
# to this script.
#
# Records:
#   F <file> <verdict> <giveup>
#   C <file> <raw DTRES-CENSUS line>
#
# Usage: census-shard.sh <tag> <list> <out.tsv> <cores> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-10}"
HEADROOM=16
BIN="${CENSUS_BIN:?set CENSUS_BIN}"
[ -x "$BIN" ] || { echo "ABORT $TAG: $BIN missing"; exit 2; }
VLIM=$((8 * 1024 * 1024))

: > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  raw=$(AXEYUM_DTRES_CENSUS=1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000)) --trace" \
          "$BIN" "$f" 2>&1)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat)$')
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | cut -c1-240)
  [ "$rc" = 124 ] && g="WRAPPER-KILLED"
  [ "$rc" = 134 ] && g="RC134-ABORT"
  [ "$rc" = 137 ] && g="SIGKILL"
  printf 'F\t%s\t%s\t%s\n' "$f" "${v:-unknown}" "${g:-none}" >> "$OUT"
  printf '%s\n' "$raw" | grep '^DTRES-CENSUS ' | while read -r line; do
    printf 'C\t%s\t%s\n' "$f" "$line" >> "$OUT"
  done
done < "$LIST"
echo "CENSUS-DONE $TAG $(grep -c '^F' "$OUT") files"
