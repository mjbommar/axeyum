#!/usr/bin/env bash
# ADR-1966 census: run ONE axeyum binary over a pinned list and record, per
# file, the verdict, `attempts=`, the route trail's last entry and the
# `give-up` line.
#
# The row that matters here is `give-up kind=Error detail=unsupported by
# backend: ...`.  At the front door an ERROR is never a verdict, so every such
# row is a rung that refused a fragment and ended the dispatch -- the live
# population of the defect, derived from BEHAVIOUR rather than from reading.
#
# Same 24 s / 8 GiB / pinned-core envelope as the tier1 board so a row here is
# comparable to a board row.
#
# Usage: census-run.sh <binary> <tag> <list-of-absolute-paths> <out.tsv> <core>
set -u
BUDGET="${BUDGET:-24}"
HEADROOM="${HEADROOM:-16}"
AX="$1"; TAG="$2"; LIST="$3"; OUT="$4"; PIN="$5"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }

printf 'file\tverdict\trc\tattempts\tdecided_by\tbound_by\tlast\ttotal_ms\tgiveup\n' > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  rl=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*')
  fld() { printf '%s\n' "$rl" | grep -oE "$1=[^ ]+" | head -1 | cut -d= -f2-; }
  att=$(fld attempts); dec=$(fld decided_by); bnd=$(fld bound_by)
  lst=$(fld last); tms=$(fld total_ms)
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${v:-none}" "$rc" "${att:-NOROUTE}" "${dec:-na}" \
    "${bnd:-na}" "${lst:-na}" "${tms:-na}" "${g:-none}" >> "$OUT"
done < "$LIST"
echo "CENSUS-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
