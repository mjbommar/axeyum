#!/usr/bin/env bash
# Re-run every probe against BOTH reference solvers and print
# `<probe> z3=<v> cvc5=<v>`.
#
# The units differ and mixing them corrupts a board: `z3 -T:<SECONDS>` versus
# `cvc5 --tlimit <MILLISECONDS>`. They are written out here so the next reader
# does not have to remember which is which.
#
# An `unknown` from a reference is NOT a pass — it is an opportunity the check
# never had. ADR-1955 measured 119 of 119 ABV files where neither reference
# decides, so this script prints the reference verdict verbatim rather than a
# "no disagreement" summary that would look identical either way.
#
# Usage: ref-probes.sh [seconds]
set -eu
SECS="${1:-24}"
MS=$((SECS * 1000))
LANE="$(cd "$(dirname "$0")" && pwd)"
CVC5="${CVC5:-/nas3/data/axeyum/harness/bin/cvc5}"

for f in "$LANE/../nested-array-ir-20260913/probes"/*.smt2 "$LANE/probes"/*.smt2; do
  z="$(z3 -T:"$SECS" "$f" 2>&1 | tail -1)"
  c="$("$CVC5" --tlimit "$MS" "$f" 2>&1 | tail -1)"
  printf '%s\tz3=%s\tcvc5=%s\n' "$(basename "$f")" "$z" "$c"
done
