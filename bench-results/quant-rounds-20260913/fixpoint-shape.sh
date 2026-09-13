#!/usr/bin/env bash
# WHAT the loop looks like when it fixpoints, so the next lane has a lever.
#
# The exit census answers "is the round ceiling binding?" (no).  This answers
# the question that replaces it: a row that reaches fixpoint at round 1 with
# the clock untouched has either nothing in its e-graph to match (a term-starved
# file -- the invention route's class) or a universal with no usable trigger.
# Those are different fixes and `AXEYUM_QPROBE`'s `egraph-fixpoint` line
# separates them:
#
#   QPROBE egraph-fixpoint round=N ground=G foralls=F patterns=P triggerless=T
#
# Usage: fixpoint-shape.sh <tag> <list> <out.tsv> <core>
set -u
BUDGET=24
HEADROOM=16
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"
AX="${AX:-/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

printf 'file\tround\tground\tforalls\tpatterns\ttriggerless\texit_kind\n' > "$OUT"
while read -r f; do
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          env AXEYUM_QPROBE=1 \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>&1)
  # The LAST fixpoint line, not the first: several ladder rungs run the loop
  # (`q:mbqi-quick`, `q:egraph`, `q:mbqi`), and taking the first would report
  # whichever rung happened to be cheapest rather than the one that decided.
  fp=$(printf '%s\n' "$raw" | grep -oE 'QPROBE egraph-fixpoint round=[0-9]+ ground=[0-9]+ foralls=[0-9]+ patterns=[0-9]+ triggerless=[0-9]+' | tail -1)
  ex=$(printf '%s\n' "$raw" | grep -oE 'QPROBE loop-exit kind=[A-Z]+' | tail -1 | cut -d= -f2)
  fld() { printf '%s\n' "$fp" | grep -oE "$1=[0-9]+" | head -1 | cut -d= -f2; }
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" \
    "$(fld round)" "$(fld ground)" "$(fld foralls)" "$(fld patterns)" \
    "$(fld triggerless)" "${ex:-na}" >> "$OUT"
done < "$LIST"
echo "FIXPOINT-SHAPE-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
