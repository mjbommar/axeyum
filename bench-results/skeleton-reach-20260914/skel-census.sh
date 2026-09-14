#!/usr/bin/env bash
# SKELETON-REACH -- the STATIC half. For every file in <list>, build the
# quantifier-free Boolean skeleton (every maximal quantified subformula
# replaced by one opaque Bool atom) and ask TWO INDEPENDENT solvers whether
# that skeleton is already unsat.
#
#   skel-census.sh <list> <out.tsv> <pin> [tlimit_s]
#
# Abstraction only WEAKENS, so `skeleton unsat` entails `original unsat`.
# A file whose skeleton is unsat can be refuted with NO instantiation of any
# kind, by any solver. That is the shape ADR-2025's shipped rung exploits.
#
# This measures the BENCHMARK, not a solver, so it needs no axeyum binary and
# no solver internals, and is checkable by any two independent implementations.
#
# WHY `shape` IS A SEPARATE COLUMN FROM `occ`.  ADR-2025's instrument reported
# every `occ=0` row as one `ABSTRACT-FAIL` bucket. That string covers TWO
# different findings and pre-registration R3 forbids sizing it unsplit:
#
#   occ=0 and the file contains NO `forall`/`exists` token at all
#       -> the shape is genuinely ABSENT. A real negative.
#   occ=0 but `forall`/`exists` DOES occur (inside `define-fun` bodies, which
#       this text-level tool refuses to abstract because a fresh constant
#       cannot track a function PARAMETER)
#       -> NOT MEASURED. The limit is the diagnostic's, not the solver's;
#          inside axeyum the parser has already expanded such definitions.
#
# `occ`/`atoms` are the abstractor's own liveness column (R13): a run that
# abstracted zero occurrences handed back the original file and its `unsat`
# would mean nothing.
set -u
LIST="$1"
OUT="$2"
PIN="${3:-1}"
TL="${4:-20}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
CVC5="${SKEL_CVC5:-/nas3/data/axeyum/harness/bin/cvc5}"
Z3="${SKEL_Z3:-z3}"
ABS="${SKEL_ABS:-$HERE/abstract-quantifiers.py}"
WORK="${SKEL_WORK:-/tmp/skel-census-$$}"

[ -x "$CVC5" ] || { echo "ABORT: cvc5 missing at $CVC5"; exit 2; }
[ -r "$ABS" ]  || { echo "ABORT: abstractor missing at $ABS"; exit 2; }
mkdir -p "$WORK"

verdict() { grep -m1 -oE '^(sat|unsat|unknown)$' || true; }

printf 'file\tshape\tocc\tatoms\tcvc5_skel\tz3_skel\tcvc5_ms\tz3_ms\n' > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  i=$((i + 1))
  S="$WORK/w.skel.smt2"
  rm -f "$S"
  meta=$(python3 "$ABS" "$CORPUS/$f" "$S" 2>&1 >/dev/null) || true
  occ=$(printf '%s' "$meta" | grep -oE 'occurrences_abstracted=[0-9]+' | cut -d= -f2)
  at=$(printf '%s' "$meta" | grep -oE 'distinct_atoms=[0-9]+' | cut -d= -f2)
  occ=${occ:-0}; at=${at:-0}

  if [ "$occ" -eq 0 ]; then
    # Split the old ABSTRACT-FAIL bucket by an observation independent of the
    # abstractor: does the SOURCE contain a quantifier token at all?
    if grep -qE '\(\s*(forall|exists)[[:space:]]' "$CORPUS/$f"; then
      printf '%s\tNOT-MEASURED-DEFINE-FUN\t0\t0\t-\t-\t-\t-\n' "$f" >> "$OUT"
    else
      printf '%s\tABSENT-NO-QUANTIFIER\t0\t0\t-\t-\t-\t-\n' "$f" >> "$OUT"
    fi
    continue
  fi

  t0=$(date +%s%N)
  cs=$(timeout $((TL * 4)) taskset -c "$PIN" "$CVC5" --tlimit $((TL * 1000)) "$S" 2>&1 | verdict)
  t1=$(date +%s%N)
  zs=$(timeout $((TL * 4)) taskset -c "$PIN" "$Z3" -T:"$TL" "$S" 2>&1 | verdict)
  t2=$(date +%s%N)

  printf '%s\tPRESENT\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$occ" "$at" \
      "${cs:-NONE}" "${zs:-NONE}" "$(((t1 - t0) / 1000000))" "$(((t2 - t1) / 1000000))" >> "$OUT"
done < "$LIST"
rm -rf "$WORK"
echo "DONE $OUT ($i rows)"
awk -F'\t' 'NR>1{
  if ($2!="PRESENT") k=$2;
  else if ($5=="unsat" && $6=="unsat") k="SKELETON-UNSAT";
  else if ($5=="unsat" || $6=="unsat") k="SKELETON-DISAGREE";
  else k="SKELETON-NOT-UNSAT";
  c[k]++ } END{for (x in c) print c[x], x}' "$OUT" | sort -rn
