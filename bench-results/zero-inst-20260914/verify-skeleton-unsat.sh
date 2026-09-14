#!/usr/bin/env bash
# ZERO-INST -- validate every file whose SHARED-ATOM skeleton came back unsat.
#
#   verify-skeleton-unsat.sh <list> <workroot> <out.tsv> [pin]
#
# Two independent things are checked, and both must hold:
#
# A. THE ABSTRACTION IS SOUND ON THIS FILE.  The shared-by-text atom map can
#    conflate two `let`-shadowed occurrences and manufacture a false unsat.
#    `fresh_skel` re-runs with one atom PER OCCURRENCE, which is
#    unconditionally a weakening.  Running it only on the shared-atom unsats
#    is COMPLETE, not a shortcut: the fresh map is strictly weaker, so a row
#    that was sat or unknown under the shared map can never become unsat
#    under the fresh one.
#
# B. THE ORIGINAL REALLY IS UNSAT, per three authorities that do not share a
#    codebase: the benchmark's own `(set-info :status ...)`, z3, and cvc5.
#    `skeleton unsat` entails `original unsat`, so ANY authority reporting
#    `sat` here is a soundness defect in the abstraction, not a curiosity.
#    No-opinion (`unknown`/absent) is recorded as its own value and never
#    counted as agreement.
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

printf 'file\tdeclared_status\tz3_orig\tcvc5_orig\tshared_skel\tfresh_skel\tfresh_occ\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  b=$(printf '%s' "$f" | tr '/' '_')
  st=$(grep -m1 -oE ':status[[:space:]]+(sat|unsat|unknown)' "$CORPUS/$f" \
       | grep -oE '(sat|unsat|unknown)$'); st="${st:-ABSENT}"

  S1="$WORK/$b.shared.smt2"
  S2="$WORK/$b.fresh.smt2"
  python3 "$HERE/abstract-quantifiers.py" "$CORPUS/$f" "$S1" 2>/dev/null >/dev/null
  meta=$(python3 "$HERE/abstract-quantifiers.py" "$CORPUS/$f" "$S2" \
           --fresh-per-occurrence 2>&1 >/dev/null) || meta='occurrences_abstracted=0'
  occ=$(printf '%s' "$meta" | grep -oE 'occurrences_abstracted=[0-9]+' | cut -d= -f2)

  zo=$(timeout 180 taskset -c "$PIN" "$Z3" -T:120 "$CORPUS/$f" 2>&1 | verdict)
  co=$(timeout 180 taskset -c "$PIN" "$CVC5" --tlimit 120000 "$CORPUS/$f" 2>&1 | verdict)
  s1=$(timeout 120 taskset -c "$PIN" "$CVC5" --tlimit 30000 "$S1" 2>&1 | verdict)
  s2=$(timeout 120 taskset -c "$PIN" "$CVC5" --tlimit 30000 "$S2" 2>&1 | verdict)

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$st" "${zo:-NONE}" "${co:-NONE}" \
      "${s1:-NONE}" "${s2:-NONE}" "${occ:-0}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
awk -F'\t' 'NR>1{print $2"\t"$3"\t"$4"\t"$5"\t"$6}' "$OUT" | sort | uniq -c
