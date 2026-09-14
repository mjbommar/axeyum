#!/usr/bin/env bash
# Re-run every MOVER three times per arm and classify it.
#
# One run of a mover is a coincidence until it repeats. The classes:
#
#   STABLE-GAIN   arm decided 3/3, base decided 0/3
#   STABLE-LOSS   base decided 3/3, arm decided 0/3
#   FLIP          both arms decided but to OPPOSITE verdicts
#   UNSTABLE      anything else -- the row churns and cannot be counted
#
# Usage: recheck-movers.sh <list> <out.tsv> <cores> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

one() {  # $1 = base|arm, $2 = file
  local raw
  if [ "$1" = base ]; then
    raw=$(env -u AXEYUM_DISTINCT_LINEAR timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  else
    raw=$(AXEYUM_DISTINCT_LINEAR=on timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  fi
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo none
}

printf 'file\tbase1\tbase2\tbase3\tarm1\tarm2\tarm3\tclass\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  b1=$(one base "$f"); a1=$(one arm "$f")
  b2=$(one base "$f"); a2=$(one arm "$f")
  b3=$(one base "$f"); a3=$(one arm "$f")
  bd=0; ad=0
  for v in "$b1" "$b2" "$b3"; do case "$v" in sat|unsat) bd=$((bd+1));; esac; done
  for v in "$a1" "$a2" "$a3"; do case "$v" in sat|unsat) ad=$((ad+1));; esac; done
  cls=UNSTABLE
  if [ "$bd" -eq 3 ] && [ "$ad" -eq 3 ] && [ "$b1" != "$a1" ]; then
    cls=FLIP
  elif [ "$ad" -eq 3 ] && [ "$bd" -eq 0 ]; then
    cls=STABLE-GAIN
  elif [ "$bd" -eq 3 ] && [ "$ad" -eq 0 ]; then
    cls=STABLE-LOSS
  elif [ "$bd" -eq 3 ] && [ "$ad" -eq 3 ]; then
    cls=STABLE-SAME
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "$b1" "$b2" "$b3" "$a1" "$a2" "$a3" "$cls" >> "$OUT"
done < "$LIST"

flips=$(awk -F'\t' 'NR>1 && $8 == "FLIP"' "$OUT" | wc -l)
echo "RECHECK-DONE $(($(wc -l < "$OUT") - 1)) mover(s)"
awk -F'\t' 'NR>1{print $8}' "$OUT" | sort | uniq -c
[ "$flips" -eq 0 ]
