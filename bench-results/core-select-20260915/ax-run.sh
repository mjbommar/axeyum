#!/usr/bin/env bash
# CORE-SELECT -- re-derive OUR verdict for one shard's files (R1).
#
#   ax-run.sh <list> <out.tsv> <pin> <bin> [budget_s] [corpus]
#
# Shipped defaults, no env levers: the population this lane is about is the one
# the SHIPPED tree is undecided on.  Columns: file, verdict, exit status, ms.
# The exit status is a column because a row that aborts is not a row that says
# `unknown`, and a sweep that records only verdicts cannot tell them apart.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
CORPUS="${6:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'file\tverdict\trc\tms\thost\tcore\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  t0=$(date +%s%N)
  raw=$(taskset -c "$PIN" timeout $((BUDGET + 40)) \
          "$AX" "$CORPUS/$f" --timeout-ms $((BUDGET * 1000)) 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "${v:-NOVERDICT}" "$rc" "$(( (t1 - t0) / 1000000 ))" "$(hostname)" "$PIN" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
