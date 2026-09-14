#!/usr/bin/env bash
# ZERO-INST -- WHICH part of cvc5 refutes these files?
#
#   strategy-isolate.sh <list> <workroot> <out.tsv> [pin]
#
# Six columns, chosen so that each one can only be explained by one mechanism:
#
#   full          cvc5, default, on the WHOLE benchmark              (baseline)
#   prep_only     `--preprocess-only` on the whole benchmark.  This exits
#                 BEFORE the solving loop, so an `unsat` here means the
#                 refutation is REWRITING/PREPROCESSING and nothing else --
#                 no SAT search, and no instantiation is even possible.
#   last          the LAST assertion alone, default settings
#   last_prep     the LAST assertion alone, `--preprocess-only`
#   last_noq      the LAST assertion alone with every quantifier module OFF
#                 (`--no-e-matching --finite-model-find=false --cegqi=false
#                  --conjecture-gen=false --full-saturate-quant=false`)
#   last_norw     the LAST assertion alone with simplification disabled
#                 (`--simplification=none --static-learning=false`)
#
# `last_noq` and `last_norw` are the MECHANISM checks, and they work in
# opposite directions.  If `last_noq` still refutes, no quantifier module was
# responsible.  If `last_norw` STOPS refuting, the rewriter was responsible --
# a flag that is silently ignored would leave the verdict unchanged, so the
# evidence for the rewriter is a verdict that MOVES, not one that stays.
set -u
LIST="$1"
WORK="$2"
OUT="$3"
PIN="${4:-2}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CORPUS="${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
CVC5="${ZERO_INST_CVC5:-/nas3/data/axeyum/harness/bin/cvc5}"

NOQ="--no-e-matching --finite-model-find=false --cegqi=false --conjecture-gen=false --full-saturate-quant=false"
NORW="--simplification=none --static-learning=false"

mkdir -p "$WORK"
verdict() { grep -m1 -oE '^(sat|unsat|unknown)$' || true; }
run() { timeout 120 taskset -c "$PIN" "$CVC5" --tlimit 30000 "$@" 2>&1 | verdict; }

printf 'id\tfull\tprep_only\tlast\tlast_prep\tlast_noq\tlast_norw\tlast_ms\n' > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  i=$((i + 1))
  b=$(printf '%02d' "$i")
  L="$WORK/$b.last.smt2"
  python3 "$HERE/extract-last-assert.py" "$CORPUS/$f" "$L" > /dev/null

  full=$(run "$CORPUS/$f")
  prep=$(timeout 120 taskset -c "$PIN" "$CVC5" --tlimit 30000 --preprocess-only "$CORPUS/$f" 2>&1 | verdict)
  t0=$(date +%s%N)
  last=$(run "$L")
  t1=$(date +%s%N)
  lprep=$(timeout 120 taskset -c "$PIN" "$CVC5" --tlimit 30000 --preprocess-only "$L" 2>&1 | verdict)
  # shellcheck disable=SC2086
  lnoq=$(run $NOQ "$L")
  # shellcheck disable=SC2086
  lnorw=$(run $NORW "$L")

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "${full:-NONE}" "${prep:-NONE}" \
      "${last:-NONE}" "${lprep:-NONE}" "${lnoq:-NONE}" "${lnorw:-NONE}" \
      "$(((t1-t0)/1000000))" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
column -t -s $'\t' "$OUT"
