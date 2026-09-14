#!/usr/bin/env bash
# M3 (our baseline, re-derived on THIS lane's base) and M2's bucket-G input, in
# ONE pass: the census row and the accumulated ground set come from the same
# invocation, so no row can be classified against a ground set from a different
# run.  Blocks 0/2 of a dump are deadline-bounded and therefore load-sensitive
# (measured: a 19% smaller dump on a differently-loaded box), so a second sweep
# would not be comparable to the first.
#
# ADR-1936 / ADR-1941: `attempts=` AND the `route-open` segment on every row; the
# OPEN SEGMENT is the discriminator, not `attempts=`.
# ADR-1950: `total_ms`/`bound_ms` so "budget exhausted" splits by WHICH budget.
# ADR-1956: the e-matching loop's three exits are distinct strings; the give-up
# detail is recorded verbatim so they stay distinct.
#
# AXEYUM_QGROUNDDUMP is set PER FILE (the writer APPENDS -- one shared path would
# concatenate every file's ground set into one unattributable blob).
#
# Usage: ours-run.sh <tag> <list-of-absolute-paths> <out.tsv> <cores> [budget_s] [dumpdir]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"; DUMPDIR="${6:-}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
AX=/nas3/data/axeyum/harness/inst-select/bin/smtcomp_cli-base
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ -n "$DUMPDIR" ] && mkdir -p "$DUMPDIR"

# LIVENESS GUARD.  A run in which EVERY row is `NONE` is what a hard division
# looks like and also what a broken invocation looks like; the first version of
# this script produced 61 of 61 NONE on UFNIA from a shell quoting bug and the
# TSV was perfectly well-formed.  So prove the invocation works BEFORE the sweep,
# and refuse to produce a file full of NONE.
#
# It probes up to PROBE_N files and needs only ONE verdict, because the first
# version probed exactly one and a SINGLE genuinely hard file killed a whole
# shard: on `UF` the head of one shard's list OOMs under the 8 GiB cap
# ("memory allocation of 1090519056 bytes failed", rc=134), which is a true
# property of that benchmark and not a broken invocation. A guard that cannot
# tell those apart deletes 34 good rows to avoid one bad one.
PROBE_N=3
probe_ok=""
probe_tried=0
while read -r probe; do
  [ -n "$probe" ] || continue
  probe_tried=$((probe_tried + 1))
  pv=$(env AXEYUM_QTRACE=1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
        bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
        "$AX" "$probe" 2>&1 | grep -m1 -oE '^(sat|unsat|unknown)$')
  if [ -n "$pv" ]; then
    echo "PROBE-OK $TAG verdict=$pv after $probe_tried file(s) on $probe"
    probe_ok=1
    break
  fi
  echo "PROBE-NO-VERDICT $TAG $probe"
  [ "$probe_tried" -ge "$PROBE_N" ] && break
done < "$LIST"
if [ "$probe_tried" -gt 0 ] && [ -z "$probe_ok" ]; then
  echo "ABORT $TAG: no verdict from any of $probe_tried probe file(s)"
  exit 4
fi

printf 'file\tverdict\trc\twall_ms\tattempts\tdecided_by\tbound_by\tlast\tbound_ms\ttotal_ms\topen_after\topen_ms\tdump_rows\tgiveup\n' > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  rel="${f#"$CORPUS"}"
  dump=""
  if [ -n "$DUMPDIR" ]; then
    dump="$DUMPDIR/$(printf '%s' "$rel" | tr '/' '_').ground"
    rm -f "$dump"
  fi
  t0=$(date +%s%N)
  # `env`, NOT a `${dump:+VAR=val}` prefix.  Bash decides what is an assignment
  # BEFORE it expands, so such a prefix becomes the COMMAND NAME and every row
  # comes back rc=127 / verdict NONE -- which is exactly what a hard division
  # looks like.  Measured: 61 of 61 UFNIA rows NONE before this was fixed.
  raw=$(env AXEYUM_QTRACE=1 ${dump:+AXEYUM_QGROUNDDUMP="$dump"} \
          timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  wall=$(( (t1 - t0) / 1000000 ))
  # A verdict-shaped line, NOT the exit status: a crash, an OOM and a watchdog
  # kill all exit non-zero and none of them is a solver opinion.
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  rl=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*')
  fld() { printf '%s\n' "$rl" | grep -oE "$1=[^ ]+" | head -1 | cut -d= -f2-; }
  att=$(fld attempts); dec=$(fld decided_by); bnd=$(fld bound_by)
  lst=$(fld last); bms=$(fld bound_ms); tms=$(fld total_ms)
  ol=$(printf '%s\n' "$raw" | grep -m1 -oE 'route-open ms=[0-9]+ after=[^ ]+')
  oms=$(printf '%s\n' "$ol" | grep -oE 'ms=[0-9]+' | head -1 | cut -d= -f2)
  oaf=$(printf '%s\n' "$ol" | grep -oE 'after=[^ ]+' | head -1 | cut -d= -f2)
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  dr=0
  [ -n "$dump" ] && [ -f "$dump" ] && dr=$(grep -c '^GROUND ' "$dump" || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "${v:-NONE}" "$rc" "$wall" "${att:-}" "${dec:-}" "${bnd:-}" "${lst:-}" \
    "${bms:-}" "${tms:-}" "${oaf:-}" "${oms:-}" "$dr" "${g:-}" >> "$OUT"
done < "$LIST"
echo "DONE $TAG $(wc -l < "$OUT") lines (incl header)"
