#!/usr/bin/env bash
# M2 input -- collect cvc5's instantiations per file.
#
# `--dump-instantiations` prints, after an UNSAT, the tuples of ground terms cvc5
# instantiated each quantified formula with.  It prints what cvc5 PRODUCED on the
# winning run, NOT a minimised set the refutation NEEDS, so what this collects is
# a SUPERSET.  That asymmetry is carried into every conclusion drawn from it: a
# small bucket-N is strong evidence, a large one is weak.
#
# Only files cvc5 actually refutes produce a dump; a file it does not decide is
# recorded in the log and produces no `.inst`, so a missing dump is never
# silently read as "no instantiations needed".
#
# Usage: inst-dump-run.sh <tag> <list-of-absolute-paths> <out.tsv> <cores> [budget_s] [dumpdir]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"; DUMPDIR="${6:-}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CVC5=/nas3/data/axeyum/harness/bin/cvc5
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$CVC5" ] || { echo "ABORT $TAG: $CVC5 missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ -n "$DUMPDIR" ] || { echo "ABORT $TAG: no dump dir given"; exit 2; }
mkdir -p "$DUMPDIR"

printf 'file\tverdict\tquantifiers\ttuples\tbytes\n' > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  rel="${f#"$CORPUS"}"
  dump="$DUMPDIR/$(printf '%s' "$rel" | tr '/' '_').inst"
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" --tlimit $((BUDGET * 1000)) --dump-instantiations \"\$1\"" \
          "$CVC5" "$f" 2>&1)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  qs=0; tp=0; by=0
  if [ "${v:-}" = "unsat" ]; then
    printf '%s\n' "$raw" > "$dump"
    qs=$(grep -c '^(instantiations ' "$dump" || true)
    tp=$(grep -cE '^[[:space:]]+\( ' "$dump" || true)
    by=$(wc -c < "$dump")
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$rel" "${v:-NONE}" "$qs" "$tp" "$by" >> "$OUT"
done < "$LIST"
echo "DONE $TAG $(wc -l < "$OUT") lines (incl header)"
