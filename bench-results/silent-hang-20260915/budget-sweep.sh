#!/usr/bin/env bash
# SILENT-HANG -- R6 explanation (a): is this a BUDGET bucket?
#
# A row that decides at 600 s was never hanging; it was working and 24 s was not
# enough.  A row that presents the identical phase reading at 24 s, 120 s and
# 600 s is doing something a bigger budget does not fix, and that is a different
# claim needing different work.  Nothing short of running it says which.
#
# One pinned core per row so the rows do not contend with each other, and the
# question is a VERDICT (decided / not), which is the one thing about a run that
# a neighbour on another core cannot change.  No time from this sweep is quoted.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
LIST="${1:-$W/lists/still-9.list}"
BUDGET="${2:-120}"
OUT="$W/ref/budget-${BUDGET}s.tsv"
CORES=(0 1 2 3 4 5 6 7 13)

printf 'file\tverdict\trc\tms\tbound_by\troute_line\tphase_in\tphase_in_ms\tdepth\tpeak_rss_kb\tgiveup_kind\tphase_line\n' > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" > "$W/lists/.one-$i.list"
  bash "$W/phase-census.sh" "$W/lists/.one-$i.list" "$W/ref/.one-$i.tsv" "${CORES[$((i % 9))]}" "$BUDGET" \
    > "$W/ref/.one-$i.log" 2>&1 &
  i=$((i + 1))
done < "$LIST"
wait
for j in $(seq 0 $((i - 1))); do
  tail -n +2 "$W/ref/.one-$j.tsv" >> "$OUT"
  rm -f "$W/ref/.one-$j.tsv" "$W/ref/.one-$j.log" "$W/lists/.one-$j.list"
done
echo "=== budget ${BUDGET}s ==="
awk -F'\t' '{printf "%-50s %-8s %-12s in=%-28s d=%s\n", substr($1,index($1,"/")+1,50), $2, $6, $7, $9}' "$OUT"
echo
awk -F'\t' 'NR>1{d = ($2=="sat"||$2=="unsat") ? "DECIDED" : "undecided"; c[d]++} END {for (k in c) print c[k], k}' "$OUT"
echo "DONE $OUT"
