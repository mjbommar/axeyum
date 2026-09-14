#!/usr/bin/env bash
# SKELETON-REACH -- is the control division's zero a MEASUREMENT or a
# guarantee?
#
# `QF_NIA` was chosen as the control because a static cross-reference says one
# of its 116 undecided rows carries a `distinct` above the pairwise cap, so the
# lever has somewhere to fire. The A/B's own liveness column then read VACUOUS.
# Exactly one of two things is true and the difference matters:
#
#   the row does not stop at ingest on the CURRENT tree   -> the cross-
#       reference was stale and the control is weak; say so
#   the row stops at ingest and the arm does not change it -> the lever
#       declines there (ADR-2000's polarity walk covers 309 of 356 sites), and
#       the control is weak for a DIFFERENT reason; say which
#
# ADR-2035's control was vacuous and its own measurement said so. This asks the
# question rather than inheriting the answer.
#
#   control-nonvacuity.sh <out.tsv>
set -u
OUT="$1"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SKEL_AX:-/nas3/data/axeyum/harness/skeleton-reach/bin/smtcomp_cli-arm}"
PIN="${PIN:-11}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

cd "$ROOT"
LANE=bench-results/skeleton-reach-20260914
# `LC_ALL=C` on BOTH sides. Without it `comm` warned "input is not in sorted
# order" on lists `sort` had just produced, because the committed list was
# sorted under a different collation. `comm` does not fail on that -- it prints
# a warning to stderr and carries on producing a POSSIBLY SHORT intersection,
# which is the shape of a silent under-count.
ROWS=$(comm -12 <(LC_ALL=C sort "$LANE/lists/undecided-QF_NIA.list") \
                <(LC_ALL=C sort "$LANE/lists/over-cap-356.list"))
if [ -z "$ROWS" ]; then
  echo "FINDING: no undecided QF_NIA row is over-cap -- the control is VACUOUS by construction"
  exit 1
fi

printf 'file\tbase_bound\tbase_giveup\tarm_bound\targ_giveup\tverdict_base\tverdict_arm\n' > "$OUT"
printf '%s\n' "$ROWS" | while IFS= read -r f; do
  [ -n "$f" ] || continue
  B=$(env -u AXEYUM_DECLARED_NAME_WINS -u AXEYUM_DISTINCT_LINEAR AXEYUM_TRACE=1 \
       timeout 90 taskset -c "$PIN" "$AX" "$CORPUS/$f" --timeout-ms 24000 2>&1)
  A=$(env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
       timeout 90 taskset -c "$PIN" "$AX" "$CORPUS/$f" --timeout-ms 24000 2>&1)
  bb=$(printf '%s\n' "$B" | grep -m1 '^; \(partial \)\?route ' | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
  ab=$(printf '%s\n' "$A" | grep -m1 '^; \(partial \)\?route ' | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
  bg=$(printf '%s\n' "$B" | grep -m1 '^; give-up ' | sed -n 's/.*detail=//p' | cut -c1-60)
  ag=$(printf '%s\n' "$A" | grep -m1 '^; give-up ' | sed -n 's/.*detail=//p' | cut -c1-60)
  bv=$(printf '%s\n' "$B" | grep -m1 -oE '^(sat|unsat|unknown)$')
  av=$(printf '%s\n' "$A" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "${bb:-NONE}" "${bg:-none}" "${ab:-NONE}" \
      "${ag:-none}" "${bv:-NONE}" "${av:-NONE}" >> "$OUT"
  echo "file      $f"
  echo "  base    bound_by=${bb:-NONE} verdict=${bv:-NONE} giveup=${bg:-none}"
  echo "  arm     bound_by=${ab:-NONE} verdict=${av:-NONE} giveup=${ag:-none}"
done
echo "DONE $OUT"
