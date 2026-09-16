#!/usr/bin/env bash
# z3 macro_finder ABLATION (ADR-2127).
#
# The source says z3's `macro_finder` is OFF by default
# (`src/params/preprocessor_params.h:37`) and is turned on for exactly two
# configuration paths: the explicit `AUFLIRA` logic
# (`src/params/smt_params.cpp:420`) and `setup_unknown(static_features&)`'s
# quantified+real fallback (`src/smt/smt_setup.cpp:845-847`, which calls
# `setup_AUFLIRA(false)`). It is explicitly commented OUT for AUFLIA/UFNIA
# with the reason "It destroys the existing patterns"
# (`src/params/smt_params.cpp:399-401`).
#
# That predicts a per-division split for the six Tier-1 divisions here:
#   macro_finder ON : AUFDTLIRA, UFDTLIRA (unmatched logic, quantified, real)
#                     AUFLIRA (matched explicitly)
#   macro_finder OFF: UFLIA, UF (unmatched logic, quantified, no real)
#                     UFNIA (matched -> setup_UFNIA -> setup_AUFLIA)
#
# A source reading is a prediction, not a measurement. This script MEASURES
# it, on the installed binary, and in doing so answers the question that
# actually sizes the work: on the files OUR ladder leaves undecided, how many
# does z3 decide, and how many of THOSE does it lose when macro finding is
# turned off? That difference is the ceiling on what a macro-inlining pass
# can be worth -- measured against a solver that already has everything else.
#
# Two arms, ONE binary, back to back on the SAME file on the SAME pinned core,
# arm order alternating per file, so ambient load cancels in the difference
# (bench-results/route-ownership-20260915/ab-run.sh established this envelope
# after load moved 23 verdicts in one division at fixed code).
#
#   arm A = z3 <file>                         (shipped default)
#   arm B = z3 smt.macro_finder=false <file>   (the ablation)
#
# Usage: z3-macro-ablation.sh <division> <list> <out.tsv> <cores> [budget_s]
set -u
DIV="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

command -v z3 >/dev/null || { echo "ABORT $DIV: no z3 on PATH"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $DIV: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ -s "$LIST" ] || { echo "ABORT $DIV: $LIST is empty; an empty run is not a null result"; exit 2; }

run_arm() {  # $1 = extra z3 args ("" for the default arm)
  local t0 t1 raw rc v
  t0=$(date +%s%N)
  if [ -z "$1" ]; then
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec z3 -T:$BUDGET \"\$0\"" "$f" 2>/dev/null)
  else
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec z3 -T:$BUDGET \"\$0\" \"\$1\"" "$f" "$1" 2>/dev/null)
  fi
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown|timeout)$')
  printf '%s\t%s\t%s' "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc"
}

printf 'division\tfile\tA_default\tA_ms\tA_rc\tB_nomacro\tB_ms\tB_rc\tfirst\tdelta\n' > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  [ -f "$f" ] || { printf '%s\t%s\tMISSING\t0\t0\tMISSING\t0\t0\tnone\tmissing\n' "$DIV" "$rel" >> "$OUT"; continue; }
  n=$((n + 1))
  if [ $((n % 2)) -eq 1 ]; then
    first=A; a=$(run_arm ""); b=$(run_arm "smt.macro_finder=false")
  else
    first=B; b=$(run_arm "smt.macro_finder=false"); a=$(run_arm "")
  fi
  av=${a%%$'\t'*}; bv=${b%%$'\t'*}
  if [ "$av" = "$bv" ]; then d=same
  elif { [ "$av" = "sat" ] || [ "$av" = "unsat" ]; } && { [ "$bv" != "sat" ] && [ "$bv" != "unsat" ]; }; then d=LOST_WITHOUT_MACRO
  elif { [ "$bv" = "sat" ] || [ "$bv" = "unsat" ]; } && { [ "$av" != "sat" ] && [ "$av" != "unsat" ]; }; then d=GAINED_WITHOUT_MACRO
  else d=DISAGREE
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$DIV" "$rel" "$a" "$b" "$first" "$d" >> "$OUT"
done < "$LIST"

if [ "$n" -eq 0 ]; then
  echo "ABORT $DIV: 0 files run -- an empty ablation is indistinguishable from a null result"
  exit 3
fi
echo "done $DIV: $n files -> $OUT"
