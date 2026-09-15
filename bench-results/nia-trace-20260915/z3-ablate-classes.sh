#!/usr/bin/env bash
# Per-lemma-class ABLATION of z3 on the QF_NIA files it decides. Lane
# NIA-TRACE, ADR-2112.
#
# WHY THIS AND NOT THE `-st` COUNTERS. A counter says a machine produced a
# conflict; it does not say the file needed it. z3 runs these as a portfolio,
# so "grobner conflicted on 61 of 76" is consistent with grobner being
# load-bearing on 61 files and with it being load-bearing on none. Worse, a
# release z3 pools basics, order, monotonicity and tangent lemmas into ONE
# counter (`lp_settings.h:127`), so the counters cannot separate the classes
# this lane most needs separated.
#
# Turning a class OFF and re-running answers both: a file that decided with the
# class and does not without it NEEDED that class. z3 exposes exactly the
# switches required (`smt.arith.nl.*`).
#
# The baseline arm runs with nothing disabled, on the same core in the same
# sweep, so "decided in baseline" is measured here rather than inherited from an
# earlier run under different load -- a file the baseline does not decide is
# excluded from every count rather than scored as a loss for every class.
#
# Plain `(check-sat)` and NOT `(check-sat-using qfnia)`: the tactic builds its
# own pipeline and does not route these parameters to the arithmetic solver, so
# an ablation under the tactic would silently measure nothing. `check-params`
# below asserts the switch actually moves something before the sweep runs.
#
# usage: z3-ablate-classes.sh <paths-file> <out.tsv> [core] [budget_s]
set -uo pipefail

PATHS=${1:?paths file}
OUT=${2:?output tsv}
CORE=${3:-1}
BUDGET=${4:-24}
KILL=$((BUDGET + 6))
ASLIMIT=${ASLIMIT:-8388608}

# name:parameter. `base` disables nothing and is the denominator.
ARMS=(
    "base:"
    "no-nra:smt.arith.nl.nra=false"
    "no-grobner:smt.arith.nl.grobner=false"
    "no-horner:smt.arith.nl.horner=false"
    "no-order:smt.arith.nl.order=false"
    "no-tangents:smt.arith.nl.tangents=false"
    "no-cross-nested:smt.arith.nl.cross_nested=false"
    "no-int-branching:smt.arith.nl.branching=false"
)

printf 'path\tarm\tverdict\twall_ms\texit\n' > "$OUT"

run_one() {  # $1 = arm label, $2 = param (may be empty), $3 = file
    local t0 t1 out rc verdict ms
    t0=$(date +%s%N)
    if [ -z "$2" ]; then
        out=$( (ulimit -v "$ASLIMIT"; timeout -k 2 "$KILL" taskset -c "$CORE" \
                z3 -T:"$BUDGET" -memory:7000 "$3") 2>&1 )
    else
        out=$( (ulimit -v "$ASLIMIT"; timeout -k 2 "$KILL" taskset -c "$CORE" \
                z3 -T:"$BUDGET" -memory:7000 "$2" "$3") 2>&1 )
    fi
    rc=$?
    t1=$(date +%s%N)
    ms=$(( (t1 - t0) / 1000000 ))
    if   grep -qx 'unsat' <<<"$out"; then verdict=unsat
    elif grep -qx 'sat' <<<"$out"; then verdict=sat
    elif grep -qx 'unknown' <<<"$out"; then verdict=unknown
    elif [ "$rc" -ge 124 ]; then verdict=timeout
    else verdict=error; fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$3" "$1" "$verdict" "$ms" "$rc" >> "$OUT"
}

# A switch that z3 silently ignores would make every ablation arm equal the
# baseline and read exactly like "no class is load-bearing". Refuse before the
# sweep unless z3 accepts each parameter.
for entry in "${ARMS[@]}"; do
    param=${entry#*:}
    [ -n "$param" ] || continue
    probe=$( (echo '(assert true)(check-sat)' | timeout 20 z3 -in "$param") 2>&1 )
    if grep -qiE 'unknown option|error|invalid' <<<"$probe"; then
        echo "ABORT: z3 rejects $param -- an ignored switch would make every arm"
        echo "  equal the baseline and read as 'no class matters'. Output: $probe"
        exit 2
    fi
done
echo "all ${#ARMS[@]} arm parameters accepted by z3" >&2

n=0
while IFS= read -r file; do
    [ -n "$file" ] || continue
    n=$((n + 1))
    for entry in "${ARMS[@]}"; do
        run_one "${entry%%:*}" "${entry#*:}" "$file"
    done
    printf 'core %s: %d files\n' "$CORE" "$n" >&2
done < "$PATHS"
printf 'core %s: ABLATION COMPLETE, %d files\n' "$CORE" "$n" >&2
