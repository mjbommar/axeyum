#!/usr/bin/env bash
# The STRENGTHENING mutant, given its best chance.
#
# `mutant-control.sh` ran it over 200 files at a 10 s budget and it produced
# ZERO decided contradictions -- it turned `sat` into `unknown`, not into
# `unsat`. That is a failed control, not a passed one, and this probe exists to
# say whether the cause is the mutant or the population.
#
# The mutant shares ONE injection across every rewritten application, so it can
# only contradict on a file with at least TWO applications that share an
# argument. This probe runs exactly the files that (a) the honest arm still
# decided `sat`, so the encoding did not already make them undecidable, and
# (b) carry >= 2 `distinct` applications -- with a budget six times longer.
#
# Usage: shared-mutant-probe.sh <list> <out.tsv> <cores> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-60}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

one() {
  local raw
  raw=$(AXEYUM_DISTINCT_LINEAR="$1" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$2" 2>/dev/null)
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo none
}

printf 'file\tarm\tshared\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  a=$(one "on:2" "$f")
  h=$(one "mutant:shared:2" "$f")
  printf '%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$h" >> "$OUT"
done < "$LIST"

flips=$(awk -F'\t' 'NR>1 && $2 == "sat" && $3 == "unsat"' "$OUT" | wc -l)
sat_rows=$(awk -F'\t' 'NR>1 && $2 == "sat"' "$OUT" | wc -l)
echo "SHARED-PROBE rows=$n arm_sat=$sat_rows decided_flips=$flips budget=${BUDGET}s"
if [ "$sat_rows" -eq 0 ]; then
  echo "FAIL: the honest arm decided no row `sat` -- this probe is blind"
  exit 1
fi
if [ "$flips" -eq 0 ]; then
  echo "FINDING: the strengthening mutant produces no DECIDED contradiction even here."
  echo "         Its decided kill is at unit scale only"
  echo "         (axeyum-solver/tests/distinct_linear_soundness.rs::the_shared_injection_mutant_breaks_the_sat)."
  exit 1
fi
exit 0
