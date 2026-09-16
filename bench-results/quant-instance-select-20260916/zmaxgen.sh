#!/usr/bin/env bash
# Positive control on the headline z3 column: re-derive `:max-generation` with
# `z3 -st` on every core and print it, so the ADR's "25 of 53 need generation
# >= 3" rests on a measurement this lane took rather than on a column it
# inherited from ADR-2113.
set -u
while IFS= read -r f; do
  [ -n "$f" ] || continue
  b=$(basename "$f")
  mg=$( ( ulimit -v 8388608; timeout -k 5 120 z3 -st "$f" 2>&1 ) \
        | sed -n 's/.*:max-generation *\([0-9]*\).*/\1/p' | tail -1 )
  printf '%s\t%s\n' "$b" "${mg:-NONE}"
done
