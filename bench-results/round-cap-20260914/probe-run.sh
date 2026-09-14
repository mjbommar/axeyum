#!/usr/bin/env bash
# ADR-2035 GATE 0 -- the ordered probe, run BEFORE the A/B is believed.
#
# ============================ POLARITY ============================
#   ARM "off" : AXEYUM_PRESAT_RESCUE is REMOVED with `env -u`  = the SHIPPED arm.
#   ARM "on"  : AXEYUM_PRESAT_RESCUE=1                         = the LEVER arm.
# `AXEYUM_PRESATPROBE=1` is set in BOTH arms: it only prints.
# ==================================================================
#
# What this answers, and what a census cannot:
#
#   1. Does a file cross the boundary at `site=preflight` (where the rescue is
#      already SHIPPED) as well as at `site=solve`?  If so the "missing wiring"
#      framing is wrong for that file -- the same correction [ADR-2030] made to
#      [ADR-2020]'s `combined.rs:86` reading.  A census records only the LAST
#      site to refuse and cannot separate "never reached a rescue" from
#      "reached one and came out the other side".
#
#   2. Does the SHIPPED 24 s path cross the boundary at all?  The 22 censused
#      observations live in `r1_lines`, i.e. inside the HELD-SET REPLAY probe
#      (`budget_ms=10000`), which re-runs a discarded ground set on its own
#      fresh budget.  [ADR-2030] drew exactly this distinction and had to turn
#      both instruments on.  A lever aimed at a population defined by the replay
#      probe, but SCORED on the shipped path, is being measured where the
#      population may not exist -- which is a candidate explanation for
#      [ADR-2020]'s 0-of-129 and [ADR-2030]'s 1-of-129 as well as for anything
#      this lane measures.  So this sweep is run TWICE: once bare (the shipped
#      path) and once with `AXEYUM_QPROBE_HELD_SET_REPLAY=10000` exported, which
#      the script inherits.  The difference between the two `solve` counts IS the
#      answer.
#
#   3. With the lever ON, does the rescue ever DECIDE?  The probe prints
#      `outcome=sat|unsat|declined`, so the mechanism is visible per crossing,
#      independently of any verdict count.  A lever whose rescue prints
#      `declined` on every crossing cannot produce a gain, and that is readable
#      here for the price of one sweep instead of a full A/B.
#
# Usage: probe-run.sh <list> <out.tsv> <core> <bin> <off|on> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; MODE="$5"; BUDGET="${6:-24}"
# The FCPROBE lines that carry the CEGAR round distribution are in the same
# stderr stream, so the raw log is kept beside the TSV rather than re-derived by
# a second sweep. `##FILE` markers let `round-distribution.py` attribute a line.
RAW="${OUT%.tsv}.fcprobe.log"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
echo "PROBE core=$PIN mode=$MODE budget=${BUDGET}s sha256=$(sha256sum "$AX" | cut -d' ' -f1)"

printf 'file\tverdict\tms\tpreflight\tsolve\trescue_ran\tout_sat\tout_unsat\tout_declined\tout_unknown\tfirst_lines\n' > "$OUT"
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  t0=$(date +%s%N)
  if [ "$MODE" = off ]; then
    raw=$(env -u AXEYUM_PRESAT_RESCUE AXEYUM_PRESATPROBE=1 \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  else
    raw=$(env AXEYUM_PRESAT_RESCUE=1 AXEYUM_PRESATPROBE=1 \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  fi
  t1=$(date +%s%N)
  printf '##FILE %s\n' "$f" >> "$RAW"
  printf '%s\n' "$raw" | grep -E 'FCPROBE|PRESATPROBE' >> "$RAW" || true
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  # Counts, not a boolean: a file consults the boundary once per CEGAR round and
  # once per width rung, so "did it happen" throws away the shape.
  pf=$(printf '%s\n' "$raw" | grep -c 'PRESATPROBE site=preflight')
  sv=$(printf '%s\n' "$raw" | grep -c 'PRESATPROBE site=solve')
  rr=$(printf '%s\n' "$raw" | grep -c 'PRESATPROBE .*rescue=ran')
  os=$(printf '%s\n' "$raw" | grep -c 'PRESATPROBE .*rescue=ran outcome=sat')
  ou=$(printf '%s\n' "$raw" | grep -c 'PRESATPROBE .*rescue=ran outcome=unsat')
  od=$(printf '%s\n' "$raw" | grep -c 'PRESATPROBE .*rescue=ran outcome=declined')
  ok=$(printf '%s\n' "$raw" | grep -c 'PRESATPROBE .*rescue=ran outcome=unknown')
  fl=$(printf '%s\n' "$raw" | grep -m2 'PRESATPROBE' | tr '\n' '|')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "$v" "$(( (t1 - t0) / 1000000 ))" "$pf" "$sv" "$rr" "$os" "$ou" "$od" "$ok" "$fl" >> "$OUT"
done < "$LIST"
echo "DONE $OUT rows=$n core=$PIN mode=$MODE"
