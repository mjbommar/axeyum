#!/usr/bin/env bash
# One pass over a pinned division list that yields BOTH the board row (our
# verdict) and the blocker census row (route fields + give-up reason) for the
# same file, at the SAME envelope the pinned boards used (24 s wall, 8 GiB
# address space, one pinned physical core).  Only axeyum runs here; the
# reference columns come from the pinned boards and are not re-derived.
#
# ADR-1936 / ADR-1941: `attempts=` AND the `route-open` segment on every row;
# the OPEN SEGMENT is the discriminator, not `attempts=`.
# ADR-1950: `total_ms` and `bound_ms` are recorded so "budget exhausted" can be
# split by WHICH budget and the remaining-budget distribution published.
# ADR-1956: the e-matching loop's three exits are distinct strings in the
# give-up detail; this records the detail verbatim so they stay distinct.
#
# `AXEYUM_QTRACE=1` adds the per-rung cumulative stderr trail so "where the
# clock went inside the quantified ladder" is answerable from this artifact
# rather than from a second sweep.  It prints only to stderr and changes no
# verdict.
#
# Usage: census-run.sh <tag> <list-of-absolute-paths> <out.tsv> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

printf 'file\tverdict\trc\twall_ms\tattempts\tdecided_by\tbound_by\tlast\tbound_ms\ttotal_ms\topen_after\topen_ms\tdeepest\tqtrace\tgiveup\n' > "$OUT"
while read -r f; do
  t0=$(date +%s%N)
  raw=$(AXEYUM_QTRACE=1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  wall=$(( (t1 - t0) / 1000000 ))
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  rl=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*')
  fld() { printf '%s\n' "$rl" | grep -oE "$1=[^ ]+" | head -1 | cut -d= -f2-; }
  att=$(fld attempts); dec=$(fld decided_by); bnd=$(fld bound_by)
  lst=$(fld last); bms=$(fld bound_ms); tms=$(fld total_ms)
  ol=$(printf '%s\n' "$raw" | grep -m1 -oE 'route-open ms=[0-9]+ after=[^ ]+')
  oms=$(printf '%s\n' "$ol" | grep -oE 'ms=[0-9]+' | head -1 | cut -d= -f2)
  oaf=$(printf '%s\n' "$ol" | grep -oE 'after=[^ ]+' | head -1 | cut -d= -f2)
  dpst=$(printf '%s\n' "$raw" | grep -m1 -oE 'deepest=[^ ]+' | cut -d= -f2)
  qt=$(printf '%s\n' "$raw" | grep -oE '^\[qtrace\] .*' \
        | sed -E 's/^\[qtrace\] ([^ ]+) \+([0-9.]+)s (.*)$/\1@\2:\3/' | tr '\n' ';' | tr '\t' ' ')
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${v:-none}" "$rc" "$wall" "${att:-NOROUTE}" "${dec:-na}" "${bnd:-na}" \
    "${lst:-na}" "${bms:-na}" "${tms:-na}" "${oaf:-na}" "${oms:-na}" "${dpst:-na}" \
    "${qt:-na}" "${g:-none}" >> "$OUT"
done < "$LIST"
echo "CENSUS-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
