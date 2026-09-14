#!/usr/bin/env bash
# Re-check the rows NO reference decided, on an IDLE host, one pinned pair.
#
# Why: the first reference pass ran six concurrent shards on s4 alongside other
# lane activity, and it read z3 = 155 where the canonical board reads 166.  Load
# can only make a deadline-bounded solver decide FEWER files, so that pass
# UNDERSTATES addressability, and the rows it understates are exactly the ones
# it called "nobody decides".  A confident "not a prize, ever" therefore has to
# be re-taken quietly before it is published.
#
# Usage: recheck-nobody.sh <list> <out.tsv> <cores>
set -u
LIST="$1"; OUT="$2"; PIN="$3"
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
printf 'file\tz3\tcvc5\tstatus\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  z=$(timeout 40 taskset -c "$PIN" "$Z3" -T:24 "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  c=$(timeout 40 taskset -c "$PIN" "$CVC5" --tlimit 24000 "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s\t%s\n' "$f" "${z:-none}" "${c:-none}" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "RECHECK_COMPLETE rows=$(( $(wc -l < "$OUT") - 1 ))"
