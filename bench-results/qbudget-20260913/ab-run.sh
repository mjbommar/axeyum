#!/usr/bin/env bash
# Interleaved per-file A/B of two `AXEYUM_QINST_EGRAPH_RETRY_SHARE` arms, which
# ALSO carries the census columns (`bound_by`, the give-up string) so the same
# sweep re-derives the blocker distribution on the tree being measured.
#
# ============================ LEVER POLARITY ==============================
# `AXEYUM_QINST_EGRAPH_RETRY_SHARE` **SHIPS OFF**. Unset -- or `off`, `0`, an
# empty value, or anything unparseable -- is the SHIPPED behaviour: the
# Skolemized e-graph retry takes a HALF slice of the remaining root deadline.
#
#   base arm  = `env -u AXEYUM_QINST_EGRAPH_RETRY_SHARE`   <- SHIPPED
#   measured  = `AXEYUM_QINST_EGRAPH_RETRY_SHARE=1`        <- the CEILING arm,
#               the retry takes the WHOLE remaining root deadline
#
# A runner COPIED from this one that keeps the polarity of a lever which ships
# ON measures the shipped arm against itself and reports a confident zero. If
# you copy this file, re-read this block against your lever's default before
# you launch anything.
# ==========================================================================
#
# ONE BINARY, two env values, so an A/B cannot accidentally compare two builds.
#
# The two arms run BACK TO BACK on the SAME file on the SAME pinned core, so
# ambient load -- which has moved 23 verdicts in one division at fixed code on
# these boxes -- cancels in the DIFFERENCE rather than landing entirely on
# whichever arm ran second. Arm order alternates per file for the same reason.
#
# Same envelope as the census and both pinned boards: 24 s wall, 8 GiB
# `ulimit -v`, one pinned physical core.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <bin> <arm-env-value> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; ARM="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

run_arm() {  # $1 = "base" | "arm"; emits verdict, ms, rc, bound_by, giveup
  local t0 t1 raw v ms rl bnd g
  t0=$(date +%s%N)
  if [ "$1" = base ]; then
    raw=$(env -u AXEYUM_QINST_EGRAPH_RETRY_SHARE timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(AXEYUM_QINST_EGRAPH_RETRY_SHARE="$ARM" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  ms=$(( (t1 - t0) / 1000000 ))
  rl=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*')
  bnd=$(printf '%s\n' "$rl" | grep -oE 'bound_by=[^ ]+' | head -1 | cut -d= -f2-)
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s' "${v:-none}" "$ms" "$rc" "${bnd:-na}" "${g:-none}"
}

printf 'file\tbase\tbase_ms\tbase_rc\tbase_bound_by\tbase_giveup\tarm\tarm_ms\tarm_rc\tarm_bound_by\tarm_giveup\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    first=base; b=$(run_arm base); a=$(run_arm arm)
  else
    first=arm;  a=$(run_arm arm);  b=$(run_arm base)
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$b" "$a" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT"
