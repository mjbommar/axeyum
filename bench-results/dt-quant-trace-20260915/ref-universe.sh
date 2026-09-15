#!/usr/bin/env bash
# DT-QUANT-TRACE -- does z3's model finder build a finite universe for a
# DATATYPE sort on these files?
#
#   ref-universe.sh <file.smt2> [tlimit_s]
#
# The brief assumed it does ("the `-v` output prints the finite universes"), and
# reading the source says it cannot: `smt_model_finder.cpp` contains zero
# occurrences of `datatype` and of `constructor` (control: `sort` = 68), and its
# only sort-driven population is gated on `m.is_uninterp(s)` at `:1700-1706`,
# which a datatype sort is not.
#
# A source reading is not a measurement, so this asks the binary. It prints what
# the model finder actually emits, with a POSITIVE CONTROL in the same run: if
# the `mbqi` / `model_finder` trace tags produce no output at all then the
# absence of a datatype universe says nothing, because nothing was traced. The
# control is whether ANY model-finder line appears.
#
# Note that a release z3 has `-tr:` compiled out; `-v:` is the one that survives.
# Both are tried and the script says which produced output.
set -u
F="$1"; TL="${2:-30}"
Z3="${DT_Z3:-z3}"
command -v "$Z3" > /dev/null || { echo "ABORT: $Z3 missing"; exit 2; }

run() {
  echo "----- $* -----"
  timeout $((TL + 20)) "$Z3" -T:"$TL" "$@" "$F" 2>&1 | head -60
}

echo "=== verdict and datatype axiom counters ==="
timeout $((TL + 20)) "$Z3" -T:"$TL" -st "$F" 2>&1 \
  | grep -E '^(sat|unsat|unknown|timeout)$|datatype-|quant-inst|max-generation'

echo
echo "=== -v:10 under MBQI only (ematching off), so any universe MUST be the model finder's ==="
out=$(timeout $((TL + 20)) "$Z3" -T:"$TL" -v:10 smt.ematching=false "$F" 2>&1)
printf '%s\n' "$out" | head -40
echo "--- lines mentioning a universe / model finder / instantiation set ---"
printf '%s\n' "$out" | grep -icE 'universe|model.finder|instantiation.set|freeze' \
  | sed 's/^/  matching lines: /'
echo "--- CONTROL: total -v:10 lines emitted at all ---"
printf '%s\n' "$out" | grep -c . | sed 's/^/  total lines: /'
echo "--- lines mentioning datatype or a constructor name ---"
printf '%s\n' "$out" | grep -icE 'datatype|constructor|qtmk' \
  | sed 's/^/  matching lines: /'
