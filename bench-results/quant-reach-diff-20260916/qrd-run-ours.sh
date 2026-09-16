#!/usr/bin/env bash
# QUANT-REACH-DIFF: run OUR engine (SHIPPED DEFAULT configuration -- no lever
# overrides) on ADR-2113's 53 reference-minimal UFLIA cores, with the same
# diagnostics ADR-2120/2133 used (AXEYUM_QTRACE + AXEYUM_QPROBE +
# AXEYUM_QPROBE_CENSUS + AXEYUM_QGROUNDDUMP), on the ORIGINAL quantified core
# (not a ground-only reconstruction -- QUANT-INSTANCE-PROBE already answered
# the ground-refutation question; this lane needs the LIVE e-matching run's
# admitted set, rejection census, and per-universal counters).
#
#   qrd-run-ours.sh <cores.list> <outdir> <pin> <bin> [budget_s]
#
# HOST NOTE: the brief pins s6 physical core pairs 1,9 / 3,11. This session's
# worktree exists only on s4 (verified: `ssh s6 ls .../worktrees/` -- no such
# directory; the repo IS checked out on s6 at the same path but this specific
# agent worktree is not). Ran on s4 instead, pinned physical pair 6,7
# (`thread_siblings_list` confirms 6-7 share one physical core on this
# 12600K). Recorded here rather than silently substituted.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$OUT/dump" "$OUT/raw"
SUMMARY="$OUT/run-summary.tsv"
printf 'core\trc\tverdict\tdecided_by\telapsed_ms\tdump_rows\n' > "$SUMMARY"

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  b="$(basename "$f")"
  dump="$OUT/dump/$b.ground"
  rm -f "$dump"
  env -u AXEYUM_QINST_POSITIVE_PATH \
    AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 \
    AXEYUM_QGROUNDDUMP="$dump" \
    timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$f" > "$OUT/raw/$b.out" 2> "$OUT/raw/$b.err"
  rc=$?
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$OUT/raw/$b.out" 2>/dev/null || true)
  decided=$(grep -m1 -oE 'decided_by=[^ ]+' "$OUT/raw/$b.out" 2>/dev/null | head -1 || true)
  ms=$(grep -m1 -oE 'total_ms=[0-9]+' "$OUT/raw/$b.out" 2>/dev/null | tail -1 || true)
  rows=0
  if [ -f "$dump" ]; then
    rows=$(grep -c '^GROUND ' "$dump" 2>/dev/null | tr -d ' ')
    rows=${rows:-0}
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$rc" "${v:-NOVERDICT}" "${decided:-NA}" "${ms:-NA}" "$rows" >> "$SUMMARY"
  printf 'RUN %3d/%s %s rc=%s v=%s rows=%s\n' "$n" "$(wc -l < "$LIST")" "$b" "$rc" "${v:-NOVERDICT}" "$rows"
done < "$LIST"
echo "RUN-OURS-DONE $n cores -> $OUT"
