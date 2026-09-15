#!/usr/bin/env bash
# Control suite for `z3-engine-trace.sh`'s `stat_of` / `engine_of` (lane
# NIA-TRACE, ADR-2112).
#
# An extractor that silently returns empty is indistinguishable from a solver
# that did not run that engine, and the first version of this sweep wrote 79
# rows of EMPTY statistic columns before anyone looked. So the extractor gets
# a positive control (a key that is present, whose value must come back exactly)
# AND a negative control (a key that is absent, which must come back empty) AND
# a prefix-collision control (`conflicts` must not be read off
# `nlsat-conflicts`), and this script exits nonzero when any of them fails.
set -uo pipefail

HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=/dev/null
# Pull the two functions out of the sweep script itself, so this tests the
# shipped code and not a copy of it.
eval "$(sed -n '/^stat_of()/,/^}/p;/^engine_of()/,/^}/p' "$HERE/z3-engine-trace.sh")"

SAMPLE='sat
(:added-eqs                       40181
 :arith-grobner-calls             462
 :arith-grobner-conflicts         179
 :arith-nla-lemmas                1758
 :arith-nra-calls                 60
 :conflicts                       647
 :nlsat-conflicts                 8748
 :memory                          19.07)'

LINEAR='unsat
(:added-eqs 12
 :arith-lower 4
 :conflicts 0
 :memory 8.10)'

fails=0
check() {
    local label=$1 got=$2 want=$3
    if [ "$got" = "$want" ]; then
        printf 'ok    %-34s [%s]\n' "$label" "$got"
    else
        printf 'FAIL  %-34s got [%s] want [%s]\n' "$label" "$got" "$want"
        fails=$((fails + 1))
    fi
}

check 'present nlsat-conflicts'         "$(stat_of "$SAMPLE" 'nlsat-conflicts')" '8748'
check 'present arith-grobner-conflicts' "$(stat_of "$SAMPLE" 'arith-grobner-conflicts')" '179'
check 'present arith-nla-lemmas'        "$(stat_of "$SAMPLE" 'arith-nla-lemmas')" '1758'
check 'present memory (decimal)'        "$(stat_of "$SAMPLE" 'memory')" '19.07'
# The collision that matters: `conflicts` is a suffix of `nlsat-conflicts` and
# of `arith-grobner-conflicts`, both of which appear FIRST in the block.
check 'no suffix collision on conflicts' "$(stat_of "$SAMPLE" 'conflicts')" '647'
check 'absent bv-bit2core'              "$(stat_of "$SAMPLE" 'bv-bit2core')" ''
check 'absent arith-horner-conflicts'   "$(stat_of "$SAMPLE" 'arith-horner-conflicts')" ''

check 'engine on a nonlinear solve'     "$(engine_of "$SAMPLE")" 'nlsat+grobner+nla'
# The negative control that makes the column mean something: a query with no
# nonlinear counter at all must not be attributed to a nonlinear engine.
check 'engine on a linear solve'        "$(engine_of "$LINEAR")" 'none'

if [ "$fails" -ne 0 ]; then
    printf '\n%d control(s) FAILED -- the statistic columns cannot be trusted\n' "$fails"
    exit 1
fi
printf '\nall controls passed\n'
