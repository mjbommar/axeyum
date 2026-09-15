#!/usr/bin/env bash
# CORE-SELECT -- build the fixed-k reference-free subsets for a list of files,
# and emit the list of subset paths for `sim-launch.sh`.
#
#   subsets-batch.sh <list> <coredir> <outdir> <out.list> [ks]
#
# Run ONLY on rows where the ceiling (our solver on the reference's own core)
# is positive.  A strategy cannot beat the ceiling, so sizing one on a row we
# would not decide even with the answer handed to us measures nothing.
set -eu
LIST="$1"; COREDIR="$2"; OUTDIR="$3"; OUTLIST="$4"; KS="${5:-1,2,5,10,25,50}"
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$OUTDIR"
: > "$OUTLIST"
ok=0; bad=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if MEM_LIMIT_GB=16 "$HERE/../../scripts/mem-run.sh" python3 "$HERE/subsets.py" \
       "$f" "$COREDIR" "$OUTDIR" --ks "$KS" > /dev/null 2>&1; then
    ok=$((ok + 1))
  else
    bad=$((bad + 1))
    echo "  SUBSET-FAILED $f"
  fi
done < "$LIST"
find "$OUTDIR" -name '*.smt2' | LC_ALL=C sort > "$OUTLIST"
echo "built=$ok failed=$bad subsets=$(grep -c . "$OUTLIST") list=$OUTLIST"
[ "$bad" -eq 0 ] || exit 12
