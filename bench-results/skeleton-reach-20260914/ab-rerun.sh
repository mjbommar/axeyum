#!/usr/bin/env bash
# SKELETON-REACH -- R5: three passes PER ARM on every moved row, then a label.
#
#   ab-rerun.sh <moved-rows.list> <out.tsv> <core> <bin> [budget_s]
#
# [ADR-2005] got +1 / -2 / +0 from three passes of BYTE-IDENTICAL code, so a
# single pass is not evidence for a moved row. Each row is run three times in
# each arm, back to back on one pinned core, and labelled from the pattern:
#
#   STABLE-GAIN   base undecided 3/3, arm decided 3/3
#   STABLE-LOSS   base decided 3/3, arm undecided 3/3
#   FLIP          any sat<->unsat disagreement anywhere  (P0)
#   UNSTABLE      anything else -- the row's own band is wider than its effect
#
# POLARITY: base is `env -u` on both levers; the arm sets both to `on`.
set -u
LIST="$1"
OUT="$2"
PIN="${3:-9}"
AX="$4"
BUDGET="${5:-24}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

one() { # $1=arm $2=file
  if [ "$1" = base ]; then
    env -u AXEYUM_DECLARED_NAME_WINS -u AXEYUM_DISTINCT_LINEAR \
      timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$2" \
      --timeout-ms $((BUDGET * 1000)) 2>&1 | grep -m1 -oE '^(sat|unsat|unknown)$' || echo NONE
  else
    env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on \
      timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$2" \
      --timeout-ms $((BUDGET * 1000)) 2>&1 | grep -m1 -oE '^(sat|unsat|unknown)$' || echo NONE
  fi
}

printf 'file\tbase1\tbase2\tbase3\tarm1\tarm2\tarm3\tlabel\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  b1=$(one base "$f"); a1=$(one arm "$f")
  a2=$(one arm "$f");  b2=$(one base "$f")
  b3=$(one base "$f"); a3=$(one arm "$f")
  L=$(BB="$b1 $b2 $b3" AA="$a1 $a2 $a3" python3 -c '
import os
b=os.environ["BB"].split(); a=os.environ["AA"].split()
dec={"sat","unsat"}
bd=[x in dec for x in b]; ad=[x in dec for x in a]
bs={x for x in b if x in dec}; as_={x for x in a if x in dec}
if bs and as_ and bs!=as_: print("FLIP")
elif not any(bd) and all(ad): print("STABLE-GAIN")
elif all(bd) and not any(ad): print("STABLE-LOSS")
elif bd==ad: print("NO-CHANGE")
else: print("UNSTABLE")
')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$b1" "$b2" "$b3" "$a1" "$a2" "$a3" "$L" >> "$OUT"
  printf '%-64s %s\n' "$(basename "$f" | cut -c1-62)" "$L"
done < "$LIST"
echo "DONE $OUT"
awk -F'\t' 'NR>1{c[$8]++} END{for (k in c) print c[k], k}' "$OUT" | sort -rn
