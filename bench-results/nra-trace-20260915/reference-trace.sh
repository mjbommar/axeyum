#!/usr/bin/env bash
# Reference-engine attribution for the QF_NRA files we do not decide
# (ADR-2110, lane NRA-TRACE).
#
# The question is not "does z3 decide it" -- the head-to-head already answered
# that. It is **which engine inside z3 decides it**, because the two candidate
# engines are a different amount of work for us:
#
#   * `nlsat` is model-constructing satisfiability with CAD projection and
#     polynomial cell construction. We have no cell construction at all.
#   * `nla_core` is incremental linearization: abstract each monomial to a
#     fresh variable, drive an LP over the abstraction, and refute with
#     tangent / order / monotonicity / Grobner lemmas. That is the same shape
#     as `crates/axeyum-solver/src/nra.rs`, so a file z3 decides THAT way is a
#     file our existing architecture can in principle reach.
#
# So each file gets three z3 arms, and the split between them IS the finding:
#
#   z3-default : the logic's own tactic (`qfnra-nlsat` for QF_NRA).
#   z3-nlsat   : `(check-sat-using qfnra-nlsat)` -- forced CAD.
#   z3-lin     : `(check-sat-using smt)` with `smt.arith.solver=6` and
#                `smt.arith.nl.nra=false` -- incremental linearization WITHOUT
#                the nlsat sub-solver. This arm is the analogue of our route.
#
# `smt.arith.nl.nra=false` is the load-bearing flag: z3's own option help says
# `arith.nl.nra` "call nra_solver when incremental linearization does not
# produce a lemma", i.e. leaving it on lets the linearization arm fall back
# into exactly the CAD engine the arm exists to exclude.
#
# cvc5 gets one arm (`--stats`), read for its `nl-ext` / `nl-cad` counters.
#
# Forcing a tactic needs the `(check-sat)` command rewritten, so each arm runs
# against a REWRITTEN COPY of the benchmark in a scratch directory; the copy is
# kept so the run is reproducible and so the rewrite can be inspected rather
# than trusted.
#
# Usage:
#   reference-trace.sh --list FILE --outdir DIR --core 1,9 \
#                      [--corpus-root DIR] [--budget-s 24] \
#                      [--cvc5 PATH] [--z3 PATH]
#
# Exit status: non-zero when any arm produced no verdict line at all for some
# file (an absent arm is a hole in the population, not a zero).
set -u

LIST=""; OUT=""; CORE=""
CORPUS_ROOT="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
BUDGET_S=24
CVC5="/nas3/data/axeyum/harness/bin/cvc5"
Z3="z3"
VLIMIT_KB=$((8 * 1024 * 1024))

while [ $# -gt 0 ]; do
  case "$1" in
    --list) LIST="$2"; shift 2 ;;
    --outdir) OUT="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    --cvc5) CVC5="$2"; shift 2 ;;
    --z3) Z3="$2"; shift 2 ;;
    *) echo "reference-trace: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in LIST OUT CORE; do
  if [ -z "${!required}" ]; then
    echo "reference-trace: --${required,,} is required" >&2
    exit 2
  fi
done

mkdir -p "$OUT/logs" "$OUT/rewritten" || exit 2
INDEX="$OUT/reference.tsv"
printf 'file\tarm\tverdict\tms\texit\n' > "$INDEX"

HAVE_CVC5=0
if [ -x "$CVC5" ]; then HAVE_CVC5=1; else
  echo "reference-trace: no cvc5 at $CVC5 -- cvc5 arm SKIPPED (recorded as 'absent')" >&2
fi

# A live probe per solver before any measurement: each has to DECIDE a file we
# already know the answer to. z3 was absent on one host earlier in this
# repository's history and 800 files scored a silent 0/200 that read exactly
# like a result.
PROBE="$OUT/probe.smt2"
printf '(set-logic QF_NRA)\n(declare-fun x () Real)\n(assert (= (* x x) 2.0))\n(assert (> x 0))\n(check-sat)\n' > "$PROBE"
probe_z3="$(timeout 20 "$Z3" -T:10 "$PROBE" 2>&1 | head -1)"
if [ "$probe_z3" != "sat" ]; then
  echo "reference-trace: z3 LIVE PROBE FAILED (got '$probe_z3')" >&2
  exit 2
fi
echo "reference-trace: z3 live probe ok ($probe_z3)" >&2
if [ "$HAVE_CVC5" -eq 1 ]; then
  probe_cvc5="$(timeout 20 "$CVC5" --tlimit=10000 "$PROBE" 2>&1 | head -1)"
  if [ "$probe_cvc5" != "sat" ]; then
    echo "reference-trace: cvc5 LIVE PROBE FAILED (got '$probe_cvc5')" >&2
    exit 2
  fi
  echo "reference-trace: cvc5 live probe ok ($probe_cvc5)" >&2
fi

verdict_of() { grep -m1 -oE '^(sat|unsat|unknown)$' -- "$1" 2>/dev/null || true; }

holes=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  abs="$CORPUS_ROOT/$rel"
  slug="$(printf '%s' "$rel" | tr '/' '_')"

  # The two forced-tactic copies. `(check-sat)` is replaced, never appended to,
  # so the copy asks exactly one question.
  nlsat_copy="$OUT/rewritten/nlsat__$slug"
  lin_copy="$OUT/rewritten/lin__$slug"
  sed 's/^(check-sat)$/(check-sat-using qfnra-nlsat)/' "$abs" > "$nlsat_copy"
  sed 's/^(check-sat)$/(check-sat-using smt)/' "$abs" > "$lin_copy"

  run_arm() {  # $1 arm, $2 input file, then the solver argv
    local arm="$1" input="$2"; shift 2
    local log="$OUT/logs/${arm}__${slug}.log"
    local t0 t1 rc v
    t0=$(date +%s%N)
    timeout $((BUDGET_S + 16)) taskset -c "$CORE" \
      bash -c "ulimit -v $VLIMIT_KB; exec \"\$@\"" _ "$@" "$input" \
      > "$log" 2>&1
    rc=$?
    t1=$(date +%s%N)
    v="$(verdict_of "$log")"
    printf '%s\t%s\t%s\t%s\t%s\n' \
      "$rel" "$arm" "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc" >> "$INDEX"
    printf '%s' "${v:-none}"
  }

  vd="$(run_arm z3-default "$abs" "$Z3" -st "-T:$BUDGET_S")"
  run_arm z3-nlsat "$nlsat_copy" "$Z3" -st "-T:$BUDGET_S" > /dev/null
  run_arm z3-lin "$lin_copy" "$Z3" -st "-T:$BUDGET_S" \
    smt.arith.solver=6 smt.arith.nl.nra=false > /dev/null
  if [ "$HAVE_CVC5" -eq 1 ]; then
    run_arm cvc5 "$abs" "$CVC5" --stats "--tlimit=$((BUDGET_S * 1000))" > /dev/null
  else
    printf '%s\t%s\t%s\t%s\t%s\n' "$rel" "cvc5" "absent" "0" "0" >> "$INDEX"
  fi

  # A file for which the DEFAULT arm produced no verdict token at all (not even
  # `unknown`) is a hole: the run neither decided nor reported that it could
  # not. That is the one outcome this loop must not swallow.
  if [ "$vd" = "none" ]; then
    echo "reference-trace: NO VERDICT LINE from z3-default on $rel" >&2
    holes=$((holes + 1))
  fi
  echo "[ref] $vd $rel"
done < "$LIST"

echo "reference-trace: $holes files with no z3-default verdict line" >&2
[ "$holes" -eq 0 ]
