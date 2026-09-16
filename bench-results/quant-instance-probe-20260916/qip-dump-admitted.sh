#!/usr/bin/env bash
# QUANT-INSTANCE-PROBE step 4 (second arm): dump OUR OWN admitted ground
# instances per core (AXEYUM_QGROUNDDUMP), then extract just the
# instance-introduced rows (generation >= 1) as candidate assertions.
#
#   qip-dump-admitted.sh <cores.list> <outdir> <pin> <bin> [budget_s]
set -u
LIST="$1"; OUTDIR="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
mkdir -p "$OUTDIR/dump" "$OUTDIR/inst"
SUMMARY="$OUTDIR/dump-summary.tsv"
printf 'core\trun_rc\tverdict\tdump_rows\tadmitted_rows\n' > "$SUMMARY"

while IFS= read -r p; do
  [ -n "$p" ] || continue
  b="$(basename "$p")"
  dump="$OUTDIR/dump/$b.ground"
  rm -f "$dump"
  AXEYUM_QTRACE=1 AXEYUM_QGROUNDDUMP="$dump" \
    timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$p" > "$OUTDIR/dump/$b.out" 2> "$OUTDIR/dump/$b.err"
  rc=$?
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$OUTDIR/dump/$b.out" 2>/dev/null || true)
  if [ -f "$dump" ]; then
    # Take only the LAST GROUNDDUMP begin..end block (the final accumulated
    # set), never an earlier snapshot -- `AXEYUM_QGROUNDDUMP` appends one
    # block per give-up point in the loop.
    lastbegin=$(grep -n '^GROUNDDUMP begin' "$dump" | tail -1 | cut -d: -f1)
    if [ -n "${lastbegin:-}" ]; then
      tail -n "+$lastbegin" "$dump" > "$OUTDIR/inst/$b.lastblock"
    else
      : > "$OUTDIR/inst/$b.lastblock"
    fi
  else
    : > "$OUTDIR/inst/$b.lastblock"
  fi
  rows=$(grep -c '^GROUND ' "$OUTDIR/inst/$b.lastblock" 2>/dev/null || echo 0)
  # gen=0 rows are original ground assertions; gen>=1 rows are ADMITTED
  # instances (qinst_egraph.rs's own comment: "a source subterm (generation
  # 0)" vs "one an admitted instance introduced").
  admitted=$(grep -E '^GROUND [0-9]+ gen=[1-9]' "$OUTDIR/inst/$b.lastblock" 2>/dev/null | wc -l | tr -d ' ')
  admitted=${admitted:-0}
  printf '%s\t%s\t%s\t%s\t%s\n' "$b" "$rc" "${v:-NOVERDICT}" "$rows" "$admitted" >> "$SUMMARY"
done < "$LIST"
echo "DONE $SUMMARY"
