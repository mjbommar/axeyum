#!/usr/bin/env bash
# Sizing pass for ADR-2131 (lane NRA-CLAUSE-LOOP), exit criterion 1.
#
# Run ONE arm of `AXEYUM_NRA_CAD` over a file list with `--trace`, through
# `scripts/ledger-run-one.sh` so the FULL stdout is kept rather than one verdict
# token (ADR-2102's reason for that script). The cause table is then read back
# out of the kept captures by `size-report.py`, which means the same run answers
# "did we decide it" and "why not" without a second sweep.
#
# Usage: size-scan.sh --root DIR --arm VALUE --list FILE --tag NAME --core N
#                     [--budget-s 24] [--corpus-root DIR]
set -u

ROOT=""; ARM=""; LIST=""; TAG=""; CORE=""; BUDGET_S=24
CORPUS_ROOT="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"

while [ $# -gt 0 ]; do
  case "$1" in
    --root) ROOT="$2"; shift 2 ;;
    --arm) ARM="$2"; shift 2 ;;
    --list) LIST="$2"; shift 2 ;;
    --tag) TAG="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    *) echo "size-scan: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in ROOT ARM LIST TAG CORE; do
  if [ -z "${!required}" ]; then echo "size-scan: --${required,,} required" >&2; exit 2; fi
done

BIN="$ROOT/bin/smtcomp_cli"
BIN_SHA="$(sha256sum "$BIN" | awk '{print $1}')"
OUTDIR="$ROOT/out/$TAG"
mkdir -p "$OUTDIR"

n=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  AXEYUM_NRA_CAD="$ARM" "$ROOT/scripts/ledger-run-one.sh" \
    --sweep-id "nra-clause-loop-size-$TAG" --arm "$ARM" \
    --binary "$BIN" --binary-sha "$BIN_SHA" \
    --file "$CORPUS_ROOT/$rel" --corpus-root "$CORPUS_ROOT" \
    --outdir "$OUTDIR" --budget-s "$BUDGET_S" --core "$CORE" \
    --ledger-dir "$ROOT/ledger-$TAG" \
    >> "$OUTDIR/rows.tsv" 2>> "$OUTDIR/run.log"
  echo "[$TAG $n] $rel" >&2
done < "$LIST"
echo "size-scan: $TAG covered $n files -> $OUTDIR" >&2
