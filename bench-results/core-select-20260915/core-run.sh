#!/usr/bin/env bash
# CORE-SELECT -- run the core census over one shard's files.
#
#   core-run.sh <list> <out.tsv> <pin> <outdir> [tlimit] [min-cap] [min-tlimit] [min-budget]
#
# `core.py` step 1 runs z3 on the SPLIT file, so its `split` column IS the
# reference verdict (R2's bucket) on a formula EQUIVALENT to the original --
# and equivalent by the same parser that defines what a conjunct is, which is
# the object the rest of the census is about.  Rows it calls `sat` or `unknown`
# are re-asked on the ORIGINAL file by `ref-run.sh`, so a bucket the split
# itself caused is visible rather than assumed away.
#
# Two caps, both OUTSIDE python, because they bound different things:
#   * `timeout ROWCAP` bounds WALL CLOCK for the whole row (`--min-budget`
#     bounds only the minimisation loop, and a bound on one phase is not a
#     bound on the row);
#   * `ulimit -v` bounds ADDRESS SPACE. `timeout` says nothing about memory --
#     a lane's expander reached 63.4 GB under exactly that misreading and took
#     the host down. The flattener here has already been measured exhausting
#     16 GiB on one 163 KB file.
# This script is STAGED (copied to /nas3) and must not reference the worktree.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; OUTDIR="$4"
TL="${5:-60}"; MINCAP="${6:-64}"; MINTL="${7:-10}"; MINBUD="${8:-600}"
HERE="$(cd "$(dirname "$0")" && pwd)"
MEM_GB="${CS_MEM_GB:-16}"
ROWCAP=$(( TL * 6 + MINBUD + 300 ))
mkdir -p "$OUTDIR"

printf 'file\tmode\tconjuncts\tsplit\tz3_core\tminimal\tmin_status\tcore_z3\tcore_cvc5\tms\thost\tcore\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  line=$(taskset -c "$PIN" timeout "$ROWCAP" \
           bash -c 'ulimit -v $(( $1 * 1024 * 1024 )); shift; exec "$@"' _ \
           "$MEM_GB" python3 "$HERE/core.py" "$f" "$OUTDIR" \
           --tlimit "$TL" --min-cap "$MINCAP" --min-tlimit "$MINTL" \
           --min-budget "$MINBUD" 2>/dev/null)
  rc=$?
  # A row that produced no line is a ROW-ABORT, never a small core and never a
  # missing row: the exit status is carried into the table.
  if [ -z "$line" ]; then
    printf '%s\tNA\tNA\tROW-ABORT:%s\tNA\tNA\tNA\tNA\tNA\tNA\t%s\t%s\n' \
      "$f" "$rc" "$(hostname)" "$PIN" >> "$OUT"
  else
    printf '%s\t%s\t%s\n' "$line" "$(hostname)" "$PIN" >> "$OUT"
  fi
done < "$LIST"
echo "DONE $OUT"
