#!/usr/bin/env bash
# z3 per-file engine trace for the QF_NIA undecided population (lane NIA-TRACE,
# ADR-2112).
#
# Three arms per file, each with its own 24 s budget, run BACK TO BACK on the
# same pinned core so ambient load cancels in the comparison:
#
#   default  z3's own strategy for the logic in the file
#   qfnia    (check-sat-using qfnia) -- the tactic z3 selects for this logic
#   nla2bv   (check-sat-using (then simplify nla2bv smt)) -- the bit-blast route
#
# For qfnia/nla2bv the original `(check-sat)` / `(get-*)` / `(exit)` commands are
# dropped and the tactic call appended, so the assertion set is the file's and
# nothing else.
#
# `-st` statistics are captured verbatim; the ENGINE column is derived from them
# (see `engine_of`), not from the verdict, so a file decided by simplification
# alone is not attributed to nlsat.
#
# usage: z3-engine-trace.sh <paths-file> <out.tsv> [core]
set -uo pipefail

PATHS=${1:?paths file}
OUT=${2:?output tsv}
CORE=${3:-1}
BUDGET=${BUDGET:-24}
KILL=$((BUDGET + 6))
# Address-space ceiling per z3 process (8 GiB), so one pathological file cannot
# take the host down. A ceiling turns an explosion into a z3 memout, which is a
# result; it does not make the work finish.
ASLIMIT=${ASLIMIT:-8388608}

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

printf 'path\tarm\tverdict\twall_ms\texit\tengine\tnlsat_conflicts\tgrobner_conflicts\tnla_lemmas\thorner_conflicts\tnra_calls\tsat_conflicts\tbv_bits\tmemory_mb\n' > "$OUT"

# `:key value` from a `-st` block, by EXACT key. Empty when the key is absent,
# which is the informative case: z3 prints a statistic only for machinery that
# actually ran.
#
# The key is matched anchored and whole (`:key` followed by whitespace), so
# `:nlsat-conflicts` cannot be read off `:nlsat-conflicts-of-something-else`,
# and the captured group stops at the first non-numeric character.
stat_of() {
    sed -n "s/^[( ]*:$2[[:space:]]\\+\\([0-9][0-9.]*\\).*/\\1/p" <<<"$1" | head -1
}

# Which nonlinear engine did REAL work, decided from those counters rather than
# from the verdict or from a key merely being present. Every QF_NIA query runs
# the SAT core and the linear arithmetic layer, so naming those tells you
# nothing; what separates the routes is which nonlinear machinery produced
# conflicts. `none` means no nonlinear counter was nonzero -- the query fell to
# simplification or linear arithmetic alone.
engine_of() {
    local stats=$1 engines=() value
    value=$(stat_of "$stats" 'nlsat-conflicts');  [ -n "$value" ] && [ "$value" != 0 ] && engines+=(nlsat)
    value=$(stat_of "$stats" 'arith-grobner-conflicts'); [ -n "$value" ] && [ "$value" != 0 ] && engines+=(grobner)
    value=$(stat_of "$stats" 'arith-horner-conflicts');  [ -n "$value" ] && [ "$value" != 0 ] && engines+=(horner)
    value=$(stat_of "$stats" 'arith-nla-lemmas');        [ -n "$value" ] && [ "$value" != 0 ] && engines+=(nla)
    value=$(stat_of "$stats" 'bv-bit2core');             [ -n "$value" ] && [ "$value" != 0 ] && engines+=(bitblast)
    if [ ${#engines[@]} -eq 0 ]; then printf 'none'; else printf '%s' "$(IFS=+; echo "${engines[*]}")"; fi
}

run_one() {
    local file=$1 arm=$2 target=$3 t0 t1 out rc
    t0=$(date +%s%N)
    out=$( (ulimit -v "$ASLIMIT"; timeout -k 2 "$KILL" \
            taskset -c "$CORE" z3 -st -T:"$BUDGET" -memory:7000 "$target") 2>&1 )
    rc=$?
    t1=$(date +%s%N)
    local ms=$(( (t1 - t0) / 1000000 ))
    local verdict
    if   grep -qx 'unsat' <<<"$out"; then verdict=unsat
    elif grep -qx 'sat'   <<<"$out"; then verdict=sat
    elif grep -qx 'unknown' <<<"$out"; then verdict=unknown
    elif [ "$rc" -ge 124 ]; then verdict=timeout
    else verdict=error; fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$file" "$arm" "$verdict" "$ms" "$rc" \
        "$(engine_of "$out")" \
        "$(stat_of "$out" 'nlsat-conflicts')" \
        "$(stat_of "$out" 'arith-grobner-conflicts')" \
        "$(stat_of "$out" 'arith-nla-lemmas')" \
        "$(stat_of "$out" 'arith-horner-conflicts')" \
        "$(stat_of "$out" 'arith-nra-calls')" \
        "$(stat_of "$out" 'conflicts')" \
        "$(stat_of "$out" 'bv-bit2core')" \
        "$(stat_of "$out" 'memory')" >> "$OUT"
}

# Strip the trailing driver commands and append a tactic call.
derive() {
    local src=$1 tactic=$2 dst=$3
    grep -vE '^[[:space:]]*\((check-sat|exit|get-model|get-info|get-value|get-unsat-core)' "$src" > "$dst"
    printf '(check-sat-using %s)\n(exit)\n' "$tactic" >> "$dst"
}

n=0
while IFS= read -r file; do
    [ -n "$file" ] || continue
    n=$((n + 1))
    run_one "$file" default "$file"
    derive "$file" 'qfnia' "$WORK/q.smt2"
    run_one "$file" qfnia "$WORK/q.smt2"
    derive "$file" '(then simplify nla2bv smt)' "$WORK/b.smt2"
    run_one "$file" nla2bv "$WORK/b.smt2"
    printf 'core %s: %d files done\n' "$CORE" "$n" >&2
done < "$PATHS"
printf 'core %s: COMPLETE, %d files\n' "$CORE" "$n" >&2
