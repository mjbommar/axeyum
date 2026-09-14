#!/usr/bin/env bash
# Measure the NOISE FLOOR: run ONE arm over a whole division, three times, and
# report how far the decided count moves at fixed code.
#
# ADR-1970 declined to ship on a `+2` whose baseline varied by 3 files at one
# commit. A gain is only a gain relative to this number, and a lane that reports
# a delta without it is reporting an unbounded quantity.
#
# This lane has a reason of its own to need it. Its CONTROL division is `UFLIA`,
# whose largest `distinct` arity is 256 -- inside the pairwise cap -- so the arm
# provably cannot change a single byte of what is parsed there. The A/B still
# moved one `UFLIA` row from `unknown` (24,233 ms) to `unsat` (3,311 ms), back to
# back on the same pinned core. That row is a measurement of the machine, not of
# the encoding, and the band below is what says so.
#
# The arm is a PARAMETER rather than fixed: run whichever arm you are about to
# quote a delta for.
#
# Usage: noise-floor.sh <list> <outdir> <tag> <cores> <bin> <base|arm> [budget_s]
set -u
LIST="$1"; OUT="$2"; TAG="$3"; PIN="$4"; AX="$5"; ARM="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$OUT"

one() {
  local raw
  if [ "$ARM" = base ]; then
    raw=$(env -u AXEYUM_DISTINCT_LINEAR timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$1" 2>/dev/null)
  else
    raw=$(AXEYUM_DISTINCT_LINEAR=on timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$1" 2>/dev/null)
  fi
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo none
}

for run in 1 2 3; do
  o="$OUT/$TAG.run$run.tsv"
  printf 'file\tverdict\n' > "$o"
  while read -r f; do
    [ -n "$f" ] || continue
    printf '%s\t%s\n' "${f#"$CORPUS"}" "$(one "$f")" >> "$o"
  done < "$LIST"
  echo "NOISE-RUN-DONE $TAG run$run -> $o"
done
echo "NOISE-DONE $TAG arm=$ARM"
