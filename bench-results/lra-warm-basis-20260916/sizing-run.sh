#!/usr/bin/env bash
# ADR-2125 sizing: how much of a `QF_LRA` file's wall clock is spent RE-SOLVING
# the simplex from scratch, and how many times.
#
# # The population is the whole pinned 200, not the 93
#
# ADR-2122's sizing ran on the 23 rows that reach the ONLINE engine, because
# that is where implied-bound propagation lives. This lever lives somewhere
# else: ADR-2111 measured `simplex_cold_restarts=0` on every traced row, so the
# online engine is ALREADY warm. The cold re-solve it named is in the OFFLINE
# lazy-SMT loop (`dpll_t::check_with_lra_dpll_within` -> `lra::decide_within` ->
# `simplex::feasible_within_sparse`), which is a different population.
#
# So the sizing population is the whole pinned draw: the 93 undecided rows AND
# the 107 decided as a CONTROL. A share of wall time measured over the undecided
# alone answers "how much do the files we lose spend re-solving", which nobody
# disputes and which cannot say whether re-solving is what separates the halves.
#
# # What is measured
#
# `simplex_cold_builds` / `simplex_cold_build_ms` / `simplex_cold_ms` /
# `simplex_cold_pivots` are this lane's own additive counters (commit
# 63d7b44e3); `cube_*` and `total_ms` already existed. The CEILING reported in
# the ADR is `simplex_cold_ms / total_ms` per file, with `total_ms` -- the route
# trail's own wall clock -- as the denominator, printed per row rather than
# pooled, because ADR-2122 measured the spread to be the finding on exactly this
# division.
#
# Usage: sizing-run.sh <shard-id> <list> <out.tsv> <cores> <bin> [budget_s]
set -u
SHARD="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing or not executable"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }

OUTDIR="$(dirname -- "$OUT")/captures-$SHARD"
mkdir -p "$OUTDIR" || exit 2

printf 'file\trc\tms\tverdict\tdecided_by\tbound_by\ttotal_ms\tattempts\tonline_probe\tlra_entries\tlra_rounds\tatoms\tcube_decisions\tcube_flips\tcube_identical\tcube_collect_ms\tcube_fm_ms\tcube_simplex_ms\tcube_simplex_calls\tcube_matrices\tcold_builds\tcold_build_ms\tcold_ms\tcold_pivots\tcapture\n' > "$OUT"

# One `key=value` field of a named `;` trail line. Prints the empty string when
# the line is absent, which is a DIFFERENT thing from `0` and is kept as such: a
# row that never reached the lazy-SMT loop reports NOTHING about it, not zero,
# and folding the two would put 100-odd rows of silence into every denominator.
field() {
  sed -n "s/^; $2 .*/&/p" -- "$1" 2>/dev/null \
    | tr ' ' '\n' \
    | sed -n "s/^$3=//p" \
    | head -1
}

while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  if [ ! -r "$f" ]; then echo "UNREADABLE $rel" >&2; continue; fi
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  t0=$(date +%s%N)
  timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$f" > "$OUTDIR/$slug.out" 2> "$OUTDIR/$slug.err"
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- "$OUTDIR/$slug.out" 2>/dev/null || true)
  o="$OUTDIR/$slug.out"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$rc" "$(( (t1 - t0) / 1000000 ))" "${v:-none}" \
    "$(field "$o" route decided_by)" \
    "$(field "$o" route bound_by)" \
    "$(field "$o" route total_ms)" \
    "$(field "$o" route attempts)" \
    "$(field "$o" lazy-smt online_probe)" \
    "$(field "$o" lazy-smt lra_entries)" \
    "$(field "$o" lazy-smt lra_rounds)" \
    "$(field "$o" lazy-smt atoms)" \
    "$(field "$o" lazy-smt cube_decisions)" \
    "$(field "$o" lazy-smt cube_flips)" \
    "$(field "$o" lazy-smt cube_identical)" \
    "$(field "$o" lazy-smt cube_collect_ms)" \
    "$(field "$o" lazy-smt cube_fm_ms)" \
    "$(field "$o" lazy-smt cube_simplex_ms)" \
    "$(field "$o" lazy-smt cube_simplex_calls)" \
    "$(field "$o" lazy-smt cube_matrices)" \
    "$(field "$o" lazy-smt simplex_cold_builds)" \
    "$(field "$o" lazy-smt simplex_cold_build_ms)" \
    "$(field "$o" lazy-smt simplex_cold_ms)" \
    "$(field "$o" lazy-smt simplex_cold_pivots)" \
    "$o" >> "$OUT"
done < "$LIST"

echo "SHARD-DONE $SHARD $(($(wc -l < "$OUT") - 1)) rows"
