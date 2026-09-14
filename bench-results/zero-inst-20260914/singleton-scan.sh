#!/usr/bin/env bash
# ZERO-INST -- for every file in a list, scan its ORIGINAL assertions and ask
# whether any ONE of them is unsat on its own.
#
#   singleton-scan.sh <list> <workroot> <out.tsv> [pin]
#
# Run against the corpus file itself, never a variant, so the answer is a
# property of the shipped benchmark.
set -u
LIST="$1"
WORK="$2"
OUT="$3"
PIN="${4:-2}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CORPUS="${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"

mkdir -p "$WORK"
: > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  i=$((i + 1))
  b=$(printf '%02d' "$i")
  line=$(python3 "$HERE/minimize-unsat-core.py" "$CORPUS/$f" "$WORK/$b" \
           --tlimit 10000 --pin "$PIN" --singleton-only 2>&1 | head -2 | tr '\n' ' ')
  printf '%s\t%s\t%s\n' "$b" "$f" "$line" >> "$OUT"
  printf '%s\t%s\n' "$b" "$line"
done < "$LIST"
echo "DONE $OUT"
