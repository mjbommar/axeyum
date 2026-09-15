#!/usr/bin/env bash
# CORE-SELECT -- hand OUR solver a SUBSET file and record the verdict (R6/R7).
#
#   sim-run.sh <list-of-subset-files> <out.tsv> <pin> <bin> [budget_s]
#
# The list holds absolute paths to already-written subset files (cores from
# `core.py`, or the fixed-k subsets from `subsets.py`), so this runner has no
# opinion about which subset it is measuring; the tag is recovered from the
# filename by the summariser.
#
# Same budget, same shipped defaults and the same pinned-core class as the
# re-derivation, so "we are undecided on the whole" and "we decide the subset"
# are comparable statements about one solver rather than two envelopes.
#
# The exit status is a COLUMN. [ADR-2045]'s arm was `losses=0` by verdict while
# creating five new aborts, so a run that records only verdicts cannot see the
# failure mode that matters most.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'subset\tverdict\trc\tms\thost\tcore\n' > "$OUT"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  t0=$(date +%s%N)
  raw=$(taskset -c "$PIN" timeout $((BUDGET + 40)) \
          "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$(basename "$p")" "${v:-NOVERDICT}" "$rc" "$(( (t1 - t0) / 1000000 ))" \
    "$(hostname)" "$PIN" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
