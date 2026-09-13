#!/usr/bin/env bash
# Measure the NOISE FLOOR: run ONE arm over a whole division, three times, and
# report how far the decided count moves at fixed code.
#
# ADR-1970 declined to ship on a `+2` whose baseline varied by 3 files at one
# commit. A gain is only a gain relative to this number, and a lane that reports
# a delta without it is reporting an unbounded quantity.
#
# The arm is deliberately a PARAMETER rather than fixed to `base`: the shipped
# arm runs strictly more code per file, so it is the arm more exposed to
# ambient load, and measuring the quieter one would understate the floor.
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
    raw=$(AXEYUM_DATATYPE_NATIVE_REFUSAL=propagate timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$1" 2>/dev/null)
  else
    raw=$(env -u AXEYUM_DATATYPE_NATIVE_REFUSAL timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
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
echo "NOISE-DONE $TAG"
