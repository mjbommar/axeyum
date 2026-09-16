#!/usr/bin/env bash
# Re-derive the QF_LRA pinned 200 list from the board and confirm it matches the
# list LRA-ATOM-SCREEN used, and that every file is readable on the NAS corpus.
set -u
REPO="$1"
OUT=/data0/axeyum/scratch/lra-model-replay-work
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

awk -F'\t' 'NR>1{print $1}' "$REPO/bench-results/board-ab-20260915/QF_LRA.tsv" | sort > "$OUT/board200.txt"
sort "$REPO/bench-results/lra-atom-screen-20260916/qflra-200.txt" > "$OUT/screen200.txt"
echo "board rows (unique): $(wc -l < "$OUT/board200.txt")"
echo "screen list rows:    $(wc -l < "$OUT/screen200.txt")"
if diff -q "$OUT/board200.txt" "$OUT/screen200.txt" > /dev/null; then
  echo "LIST MATCH: identical"
else
  echo "LIST MISMATCH:"
  diff "$OUT/board200.txt" "$OUT/screen200.txt" | head -20
fi
cp "$OUT/screen200.txt" "$OUT/qflra-200.txt"

miss=0
while read -r f; do
  if [ ! -r "$CORPUS/$f" ]; then echo "MISSING $f"; miss=$((miss+1)); fi
done < "$OUT/qflra-200.txt"
echo "corpus missing: $miss"
