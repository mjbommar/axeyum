#!/usr/bin/env bash
# M1 -- the REFERENCE ABLATION.  For each file, run cvc5 in four arms and record
# the verdict of each.  This measures CVC5's instantiation strategies, not ours,
# and it is the only step in this lane that does not depend on our own
# instrumentation.
#
#   default      (no flags)                        the reference verdict
#   ematch       --no-enum-inst --no-cegqi         instances reachable BY E-MATCHING
#   noematch     --no-e-matching                   e-matching NOT NECESSARY
#   neither      both of the above                 neither route necessary
#
# WHAT AN ARM PROVES, stated here because the asymmetry is the whole point:
# a refutation in `ematch` proves the instances ARE e-matchable.  A FAILURE in
# `ematch` proves nothing about e-matching in general -- cvc5's e-matching is one
# implementation with its own trigger inference, and a different one could
# succeed.  The arms are NOT a partition; a file may refute in all four.
#
# Same envelope as the census that produced the population: 24 s wall, 8 GiB
# address space, one pinned physical core.  cvc5's --tlimit is MILLISECONDS
# (z3's -T: is seconds); the wrapper `timeout` is the backstop for an arm that
# ignores its own limit.
#
# Usage: ref-ablation-run.sh <tag> <list-of-absolute-paths> <out.tsv> <cores> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CVC5=/nas3/data/axeyum/harness/bin/cvc5
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$CVC5" ] || { echo "ABORT $TAG: $CVC5 missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

# One arm on one file.  Echoes "<verdict> <wall_ms>"; verdict is NONE when the
# run produced no verdict-shaped line at all, which is DISTINCT from `unknown`
# -- a crash, an OOM and a watchdog kill all land there and must not be read as
# a solver opinion.
run_arm() {
  local f="$1"; shift
  local t0 t1 raw v
  t0=$(date +%s%N)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" --tlimit $((BUDGET * 1000)) \"\$@\"" \
          "$CVC5" "$@" "$f" 2>&1)
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s' "${v:-NONE}" "$(( (t1 - t0) / 1000000 ))"
}

printf 'file\tdefault\tdefault_ms\tematch\tematch_ms\tnoematch\tnoematch_ms\tneither\tneither_ms\tstatus\n' > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  # The declared :status of the benchmark, read from the SOURCE.  Anchored on the
  # `(set-info :status ...)` form and NOT on a `$`-anchored pattern -- the copy of
  # this check in dispatch-decline-audit-20260913 piped the whole line into a
  # `$`-anchored grep and matched nothing on every file, always.
  st=$(grep -m1 -oE '\(set-info :status +(sat|unsat|unknown)' "$f" 2>/dev/null \
        | grep -oE '(sat|unsat|unknown)$')
  d=$(run_arm "$f")
  e=$(run_arm "$f" --no-enum-inst --no-cegqi)
  n=$(run_arm "$f" --no-e-matching)
  b=$(run_arm "$f" --no-e-matching --no-enum-inst --no-cegqi)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$d" "$e" "$n" "$b" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "DONE $TAG $(wc -l < "$OUT") lines (incl header)"
