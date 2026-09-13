#!/usr/bin/env bash
# Re-run every MOVED row THREE TIMES PER ARM, back to back on one pinned core.
#
# A single per-file A/B pass cannot tell a real gain from an ambient one. ADR-1966
# measured 11 of 18 moved rows outside its target division as ambient -- they
# vanished on re-check -- so a lane that reports its first pass is reporting a
# number that is, historically, about 40 % noise on the rows it did not verify.
#
# A row is STABLE only if all three runs of an arm agree with each other. A row
# that disagrees with itself is reported as UNSTABLE and is not counted either
# way, rather than being resolved by majority -- a 2:1 split is a measurement
# that did not converge, not a verdict.
#
# Usage: recheck-movers.sh <movers.tsv: file<TAB>base<TAB>arm> <out.tsv> <cores> <bin> [budget_s]
set -u
IN="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

one() {  # $1 = base|arm  $2 = file
  local raw
  if [ "$1" = base ]; then
    raw=$(AXEYUM_DATATYPE_NATIVE_REFUSAL=propagate timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  else
    raw=$(env -u AXEYUM_DATATYPE_NATIVE_REFUSAL timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  fi
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo none
}

printf 'file\tfirst_base\tfirst_arm\tb1\tb2\tb3\ta1\ta2\ta3\tverdict\n' > "$OUT"
while IFS=$'\t' read -r rel fb fa; do
  [ -n "$rel" ] || continue
  f="$CORPUS$rel"
  [ -f "$f" ] || { echo "MISSING $rel"; continue; }
  b1=$(one base "$f"); a1=$(one arm "$f")
  b2=$(one base "$f"); a2=$(one arm "$f")
  b3=$(one base "$f"); a3=$(one arm "$f")
  if [ "$b1" != "$b2" ] || [ "$b2" != "$b3" ] || [ "$a1" != "$a2" ] || [ "$a2" != "$a3" ]; then
    v=UNSTABLE
  else
    bd=no; ad=no
    case "$b1" in sat|unsat) bd=yes;; esac
    case "$a1" in sat|unsat) ad=yes;; esac
    if [ "$bd" = no ] && [ "$ad" = yes ]; then v=STABLE-GAIN
    elif [ "$bd" = yes ] && [ "$ad" = no ]; then v=STABLE-LOSS
    elif [ "$bd" = yes ] && [ "$ad" = yes ] && [ "$b1" != "$a1" ]; then v=FLIP
    else v=NO-MOVE; fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$fb" "$fa" "$b1" "$b2" "$b3" "$a1" "$a2" "$a3" "$v" >> "$OUT"
done < "$IN"
echo "RECHECK-DONE -> $OUT"
