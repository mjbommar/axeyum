#!/usr/bin/env bash
# INTERLEAVED per-file A/B for the smallest-witness lever.
#
# LEVER POLARITY, stated in the runner header because copying the wrong one
# measures the shipped arm against itself and reports a confident zero:
#
#     AXEYUM_QINST_SMALLEST_WITNESS  SHIPS OFF.
#     off / 0 / false / empty / unparseable / absent  ->  SHIPPED behaviour (base)
#     any other value (we use 1)                      ->  THE ARM UNDER TEST
#
# So the BASE arm runs with the variable UNSET and the ARM runs with it set to 1.
# One binary, two env values -- never two builds.
#
# Both arms run back to back on the SAME file on the SAME pinned physical core,
# with the ORDER ALTERNATING per file, because ambient load has moved 23 verdicts
# in one division at fixed code on these boxes.  24 s wall, 8 GiB `ulimit -v`.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
AX=/nas3/data/axeyum/harness/inst-select/bin/smtcomp_cli-lever
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

# arm: "" = base (variable unset), "1" = the arm under test.
run_arm() {
  local f="$1" val="$2" t0 t1 raw v
  t0=$(date +%s%N)
  if [ -z "$val" ]; then
    raw=$(env -u AXEYUM_QINST_SMALLEST_WITNESS timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>&1)
  else
    raw=$(env AXEYUM_QINST_SMALLEST_WITNESS="$val" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>&1)
  fi
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s' "${v:-NONE}" "$(( (t1 - t0) / 1000000 ))"
}

printf 'file\tbase\tbase_ms\tarm\tarm_ms\torder\tstatus\n' > "$OUT"
i=0
while read -r f; do
  [ -n "$f" ] || continue
  st=$(grep -m1 -oE '\(set-info :status +(sat|unsat|unknown)' "$f" 2>/dev/null \
        | grep -oE '(sat|unsat|unknown)$')
  if [ $((i % 2)) -eq 0 ]; then
    b=$(run_arm "$f" ""); a=$(run_arm "$f" "1"); ord=base-first
  else
    a=$(run_arm "$f" "1"); b=$(run_arm "$f" ""); ord=arm-first
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$b" "$a" "$ord" "${st:-none}" >> "$OUT"
  i=$((i + 1))
done < "$LIST"
echo "DONE $TAG $(wc -l < "$OUT") lines (incl header)"
