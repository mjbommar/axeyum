#!/usr/bin/env bash
# The blocker census over the WINNABLE set: every file in the pinned 200 where
# axeyum returned `unknown` and at least one reference (z3, cvc5) decided.
# Not a sample of it -- the whole set.
#
# ADR-1936: this records `attempts=` from `--trace`'s `; route` line on EVERY
# row.  A row whose dispatch did not reach the end of the ladder is
# UNCLASSIFIED and must never be reported by its give-up reason.  `; route` is
# printed even when the dispatch stops early, and a row with NO route trail at
# all is its own case (killed during INGEST, which --timeout-ms does not bound).
#
# Same 24 s / 8 GiB / pinned-core envelope as the board so a census row is
# comparable to the board row it came from.  Only axeyum runs here, so there is
# no interleaving to preserve.
#
# Usage: census-run.sh <tag> <list-of-absolute-paths> <out.tsv> <cores>
set -u
BUDGET=24
HEADROOM=16
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"
AX=/nas3/data/axeyum/harness/fpbv-divisions/bin/smtcomp_cli
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

# `open_after` / `open_ms` come from the `route-open` line:
#
#   ; partial route-open ms=24596 after=dl-online attributed_ms=401 \
#     note: bound_by is NOT the answer: most of the budget is in the open segment
#
# That is the instrument that names the DEADLINE-BLIND rung when `attempts=` is
# low: the ladder stopped recording after `after=`, and the whole budget went
# into a segment no route attempt covers.  Without it an UNCLASSIFIED row says
# only "the dispatch stopped", not where.  `deepest` is the phase breadcrumb's
# answer to the same question from the other side.
printf 'file\tverdict\trc\tattempts\tdecided_by\tbound_by\tlast\tbound_ms\ttotal_ms\topen_after\topen_ms\tdeepest\tgiveup\n' > "$OUT"
while read -r f; do
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  # `; route decided_by=X bound_by=Y last=Z bound_ms=N total_ms=N attempts=N`
  # and its `; partial route ...` form on a watchdog kill.
  rl=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*')
  fld() { printf '%s\n' "$rl" | grep -oE "$1=[^ ]+" | head -1 | cut -d= -f2-; }
  att=$(fld attempts); dec=$(fld decided_by); bnd=$(fld bound_by)
  lst=$(fld last); bms=$(fld bound_ms); tms=$(fld total_ms)
  ol=$(printf '%s\n' "$raw" | grep -m1 -oE 'route-open ms=[0-9]+ after=[^ ]+')
  oms=$(printf '%s\n' "$ol" | grep -oE 'ms=[0-9]+' | head -1 | cut -d= -f2)
  oaf=$(printf '%s\n' "$ol" | grep -oE 'after=[^ ]+' | head -1 | cut -d= -f2)
  dpst=$(printf '%s\n' "$raw" | grep -m1 -oE 'deepest=[^ ]+' | cut -d= -f2)
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${v:-none}" "$rc" "${att:-NOROUTE}" "${dec:-na}" "${bnd:-na}" \
    "${lst:-na}" "${bms:-na}" "${tms:-na}" "${oaf:-na}" "${oms:-na}" "${dpst:-na}" \
    "${g:-none}" >> "$OUT"
done < "$LIST"
echo "CENSUS-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
