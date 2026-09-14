#!/usr/bin/env bash
# Interleaved per-file A/B of the two `AXEYUM_DISTINCT_LINEAR` arms (ADR-2000).
#
# ONE BINARY, two env values, so an A/B cannot accidentally compare two builds.
#
# **POLARITY OF THIS LEVER: IT SHIPS OFF.** The commit under measurement leaves
# `AXEYUM_DISTINCT_LINEAR` unset by default, and an unset value is the
# pre-ADR-2000 pairwise expansion. So:
#
#   * the `base` (shipped, pre-ADR-2000) arm runs with the variable UNSET
#     (`env -u AXEYUM_DISTINCT_LINEAR`)
#   * the `arm`  (candidate)            arm sets `AXEYUM_DISTINCT_LINEAR=on`
#
# This is the SAME polarity as ADR-1970's and ADR-1975's runners and the
# OPPOSITE of ADR-1980's, whose lever ships ON and whose `base` therefore sets a
# value. Copying ADR-1980's runner without flipping this measures the shipped
# arm against itself and reports a confident zero.
#
# The two arms run BACK TO BACK on the SAME file on the SAME pinned core, so
# ambient load -- which has moved 23 verdicts in one division at fixed code on
# these boxes -- cancels in the DIFFERENCE rather than landing entirely on
# whichever arm ran second. Arm order alternates per file for the same reason.
#
# Same envelope as the census and both pinned boards: 24 s wall, 8 GiB
# `ulimit -v`, one pinned physical core.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s] [arm_value]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"; ARMVAL="${7:-on}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

run_arm() {  # $1 = "base" | "arm"
  local t0 t1 raw v ms rc
  t0=$(date +%s%N)
  if [ "$1" = base ]; then
    raw=$(env -u AXEYUM_DISTINCT_LINEAR timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(AXEYUM_DISTINCT_LINEAR="$ARMVAL" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  ms=$(( (t1 - t0) / 1000000 ))
  printf '%s\t%s\t%s' "${v:-none}" "$ms" "$rc"
}

printf 'file\tbase\tbase_ms\tbase_rc\tarm\tarm_ms\tarm_rc\tfirst\tstatus\n' > "$OUT"
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
echo "AB-DONE $TAG $n files arm=$ARMVAL -> $OUT"
