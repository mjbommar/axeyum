#!/usr/bin/env bash
# ZERO-INST -- THE core measurement of this lane.
#
#   skeleton-probe.sh <list> <workroot> <out.tsv> [pin]
#
# For every file: build the QUANTIFIER-FREE BOOLEAN SKELETON (every maximal
# quantified subformula replaced by one opaque Bool atom) and ask two
# INDEPENDENT solvers whether that skeleton is already unsat.
#
# Abstraction only weakens, so `skeleton unsat` entails `original unsat`.
# A file whose skeleton is unsat needs NO instantiation of any kind, by any
# solver: the refutation is available before the first instantiation round.
#
# Two authorities, because a wrong `unsat` from one solver's preprocessor is
# exactly the failure this claim would be built on.  Disagreement is printed,
# never reconciled.
#
# `occ=` is the mechanism check on the ABSTRACTION ITSELF: a run that
# abstracted zero occurrences has produced the original file back and its
# `unsat` would mean nothing.  The abstractor exits 3 in that case and the
# row records ABSTRACT-FAIL.
set -u
LIST="$1"
WORK="$2"
OUT="$3"
PIN="${4:-2}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CORPUS="${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
CVC5="${ZERO_INST_CVC5:-/nas3/data/axeyum/harness/bin/cvc5}"
Z3="${ZERO_INST_Z3:-z3}"

mkdir -p "$WORK"
verdict() { grep -m1 -oE '^(sat|unsat|unknown)$' || true; }

printf 'id\tocc\tatoms\tcvc5_skeleton\tz3_skeleton\tcvc5_skel_ms\tfile\n' > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  i=$((i + 1))
  b=$(printf '%02d' "$i")
  S="$WORK/$b.skel.smt2"
  meta=$(python3 "$HERE/abstract-quantifiers.py" "$CORPUS/$f" "$S" 2>&1 >/dev/null) || {
    printf '%s\tABSTRACT-FAIL\t-\t-\t-\t-\t%s\n' "$b" "$f" >> "$OUT"; continue; }
  occ=$(printf '%s' "$meta" | grep -oE 'occurrences_abstracted=[0-9]+' | cut -d= -f2)
  at=$(printf '%s' "$meta" | grep -oE 'distinct_atoms=[0-9]+' | cut -d= -f2)

  t0=$(date +%s%N)
  cs=$(timeout 120 taskset -c "$PIN" "$CVC5" --tlimit 30000 "$S" 2>&1 | verdict)
  t1=$(date +%s%N)
  zs=$(timeout 120 taskset -c "$PIN" "$Z3" -T:30 "$S" 2>&1 | verdict)

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$occ" "$at" "${cs:-NONE}" \
      "${zs:-NONE}" "$(((t1-t0)/1000000))" "$f" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
cut -f1-6 "$OUT" | column -t -s $'\t'
