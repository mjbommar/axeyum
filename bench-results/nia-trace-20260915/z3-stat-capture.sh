#!/usr/bin/env bash
# Captures z3's FULL `-st` block, verbatim, for every file in a list, in LONG
# form (one row per file per statistic key). Lane NIA-TRACE, ADR-2112.
#
# Long form, and every key rather than a chosen column set, for one reason: the
# bucketing question changed once already in this lane, and a sweep that keeps
# only the columns its author thought of has to be re-run each time it does.
# Bucketing is done offline against this file.
#
# It runs ONE arm -- `(check-sat-using qfnia)`, the tactic z3 selects for this
# logic and the arm that decided most -- on files z3 is already known to
# decide, so the sweep is short and every row carries a real statistic block. A
# file that does NOT decide here is recorded with `__verdict__` and no counters,
# rather than dropped: a tool that omits rather than refuses turns its output
# into a measurement of the accepted subset.
#
# usage: z3-stat-capture.sh <paths-file> <out.tsv> [core] [budget_s]
set -uo pipefail

PATHS=${1:?paths file}
OUT=${2:?output tsv}
CORE=${3:-1}
BUDGET=${4:-24}
KILL=$((BUDGET + 6))
ASLIMIT=${ASLIMIT:-8388608}

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

printf 'path\tkey\tvalue\n' > "$OUT"

n=0
while IFS= read -r file; do
    [ -n "$file" ] || continue
    n=$((n + 1))

    # Same derivation as `z3-engine-trace.sh`: drop the driver commands, append
    # the tactic call, so the assertion set is the file's and nothing else.
    grep -vE '^[[:space:]]*\((check-sat|exit|get-model|get-info|get-value|get-unsat-core)' \
        "$file" > "$WORK/q.smt2"
    printf '(check-sat-using qfnia)\n(exit)\n' >> "$WORK/q.smt2"

    out=$( (ulimit -v "$ASLIMIT"; timeout -k 2 "$KILL" \
            taskset -c "$CORE" z3 -st -T:"$BUDGET" -memory:7000 "$WORK/q.smt2") 2>&1 )

    if grep -qx 'unsat' <<<"$out"; then verdict=unsat
    elif grep -qx 'sat' <<<"$out"; then verdict=sat
    elif grep -qx 'unknown' <<<"$out"; then verdict=unknown
    else verdict=timeout; fi
    printf '%s\t__verdict__\t%s\n' "$file" "$verdict" >> "$OUT"

    # Every `:key value` pair in the block, whatever it is. The key set differs
    # per file -- z3 prints a counter only for machinery that ran -- and that
    # ABSENCE is the signal, so nothing is defaulted to zero here.
    sed -n 's/^[( ]*:\([a-zA-Z0-9_-]\+\)[[:space:]]\+\([0-9][0-9.]*\).*/\1\t\2/p' <<<"$out" \
        | while IFS=$'\t' read -r key value; do
            printf '%s\t%s\t%s\n' "$file" "$key" "$value" >> "$OUT"
        done

    printf 'core %s: %d files\n' "$CORE" "$n" >&2
done < "$PATHS"
printf 'core %s: CAPTURE COMPLETE, %d files\n' "$CORE" "$n" >&2
