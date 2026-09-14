#!/usr/bin/env bash
# ZERO-INST -- build the GROUND-only and QUANTIFIED-only variant of every file
# in a list, into $OUTDIR/ground and $OUTDIR/quant, numbered by list position.
#
#   make-variants.sh <list> <outdir>
#
# The numbering is the join key for every downstream table in this lane, and
# $OUTDIR/index.tsv records it so a row can always be traced back to its file.
set -eu
LIST="$1"
OUT="$2"
HERE="$(cd "$(dirname "$0")" && pwd)"
CORPUS="${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"

mkdir -p "$OUT/ground" "$OUT/quant"
: > "$OUT/index.tsv"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  i=$((i + 1))
  b=$(printf '%02d' "$i")
  python3 "$HERE/split-assertions.py" "$CORPUS/$f" ground    > "$OUT/ground/$b.smt2"
  python3 "$HERE/split-assertions.py" "$CORPUS/$f" quantified > "$OUT/quant/$b.smt2"
  printf '%s\t%s\n' "$b" "$f" >> "$OUT/index.tsv"
done < "$LIST"
echo "made $i variants in $OUT"
