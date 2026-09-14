#!/usr/bin/env bash
# ZERO-INST -- the decisive question for the nine files cvc5 refutes with ZERO
# instantiation tuples: is the QUANTIFIER-FREE part of the file already unsat?
#
#   probe-ground-part.sh <variant-dir> <out.tsv> [pin-core]
#
# Three columns per file, and the third is the one that makes the first two
# a measurement rather than a guess:
#
#   cvc5_ground    -- cvc5 on the ground assertions ALONE
#   z3_ground      -- an INDEPENDENT authority on the same file, because a
#                     rewrite bug in one solver's preprocessor would give a
#                     wrong `unsat` here and nothing downstream would catch it
#   cvc5_quantonly -- the QUANTIFIED assertions ALONE.  This is the
#                     non-vacuity control: if the ground part is unsat AND the
#                     quantified part alone is also unsat, the split proves
#                     nothing about which half carries the refutation.
#
# cvc5 --tlimit is MILLISECONDS; z3 -T: is SECONDS.  Both are set to 30 s.
set -u
VAR="$1"
OUT="$2"
PIN="${3:-2}"
CVC5="${ZERO_INST_CVC5:-/nas3/data/axeyum/harness/bin/cvc5}"
Z3="${ZERO_INST_Z3:-z3}"
[ -x "$CVC5" ] || { echo "ABORT: $CVC5 missing"; exit 2; }

verdict() { grep -m1 -oE '^(sat|unsat|unknown)$' || true; }

printf 'id\tcvc5_ground\tcvc5_ground_ms\tz3_ground\tz3_ground_ms\tcvc5_quantonly\n' > "$OUT"
for g in "$VAR"/ground/*.smt2; do
  b=$(basename "$g" .smt2)
  q="$VAR/quant/$b.smt2"

  t0=$(date +%s%N)
  cg=$(timeout 90 taskset -c "$PIN" "$CVC5" --tlimit 30000 "$g" 2>&1 | verdict)
  t1=$(date +%s%N)
  zg=$(timeout 90 taskset -c "$PIN" "$Z3" -T:30 "$g" 2>&1 | verdict)
  t2=$(date +%s%N)
  cq=$(timeout 90 taskset -c "$PIN" "$CVC5" --tlimit 30000 "$q" 2>&1 | verdict)

  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "${cg:-NONE}" "$(((t1-t0)/1000000))" \
      "${zg:-NONE}" "$(((t2-t1)/1000000))" "${cq:-NONE}" >> "$OUT"
done
echo "DONE $OUT"
column -t -s $'\t' "$OUT"
