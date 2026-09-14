#!/usr/bin/env bash
# Reference verdicts on the SAME files, the SAME budget, the SAME pinned core.
#
# This is what makes a row ADDRESSABLE (R3): a file we do not decide is only a
# prize if some reference decides it.  Rows nobody decides are reported
# separately and never counted toward a gap.
#
# THE UNITS DIFFER AND MIXING THEM SILENTLY CORRUPTS THE RESULT:
#   z3   -T:<SECONDS>
#   cvc5 --tlimit <MILLISECONDS>
#
# Usage: ref-run.sh <tag> <list> <out.tsv> <cores> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"
HEADROOM=16
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5

[ -x "$Z3" ]   || { echo "ABORT $TAG: z3 missing";   exit 2; }
[ -x "$CVC5" ] || { echo "ABORT $TAG: cvc5 missing"; exit 2; }
[ -s "$OUT" ]  && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }

printf 'file\tz3\tz3_ms\tcvc5\tcvc5_ms\tstatus\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')

  t0=$(date +%s%N)
  z=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" "$Z3" -T:$BUDGET "$f" 2>/dev/null \
        | grep -m1 -oE '^(sat|unsat|unknown)$')
  t1=$(date +%s%N)

  t2=$(date +%s%N)
  c=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" "$CVC5" --tlimit $((BUDGET * 1000)) "$f" 2>/dev/null \
        | grep -m1 -oE '^(sat|unsat|unknown)$')
  t3=$(date +%s%N)

  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" \
    "${z:-none}" "$(( (t1 - t0) / 1000000 ))" \
    "${c:-none}" "$(( (t3 - t2) / 1000000 ))" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "REF_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
