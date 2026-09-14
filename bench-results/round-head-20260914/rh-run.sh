#!/usr/bin/env bash
# Lane ROUND-HEAD: the exit census and the held-set replay, INTERLEAVED per file.
#
# TWO ARMS, ONE BINARY, TWO ENV VALUES -- never two builds.
#
#   arm C (census)  AXEYUM_QPROBE=1                          -- the shipped run.
#   arm R (replay)  AXEYUM_QPROBE=1
#                   AXEYUM_QPROBE_HELD_SET_REPLAY=<ms>       -- the instrument.
#
# POLARITY, stated here because copying the wrong runner measures the shipped
# arm against itself: `AXEYUM_QPROBE_HELD_SET_REPLAY` is OFF when the variable
# is UNSET, EMPTY, zero, or unparseable. Arm C runs it UNSET (`env -u`), arm R
# runs it set to a positive integer.
#
# ARM R PERTURBS THE RUN AND IS NOT A VERDICT ARM. The replay burns real wall
# clock inside the solve after the rung deadline has already passed, so later
# rungs of the same query see less of the root budget. Arm R's VERDICT column is
# recorded but must never be differenced against arm C's; only its
# `held-set-replay` lines are load-bearing. Arm C is the verdict arm.
#
# Both arms run back to back on the SAME file on the SAME pinned physical core
# with the ORDER ALTERNATING per file, because ambient load has moved 23
# verdicts in one division at fixed code on these boxes.
#
# Usage: rh-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s] [replay_ms]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"; REPLAY="${7:-8000}"
HEADROOM=16
# Arm R may emit several replays per file; each is capped at REPLAY ms, so the
# outer kill has to be generous or a slow file reads as a harness failure.
RHEADROOM=180
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

# Collapse a multi-line capture into one TSV cell, `;`-separated, tabs stripped.
join1() { tr '\t' ' ' | tr '\n' ';' | sed 's/;$//'; }

run_c() {
  local f="$1" t0 t1 raw rc
  t0=$(date +%s%N)
  raw=$(env -u AXEYUM_QPROBE_HELD_SET_REPLAY AXEYUM_QPROBE=1 \
          timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  C_V=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  C_V="${C_V:-NONE}"
  C_RC=$rc
  C_MS=$(( (t1 - t0) / 1000000 ))
  C_GIVEUP=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  C_GIVEUP="${C_GIVEUP:-none}"
  C_EXITS=$(printf '%s\n' "$raw" | grep -oE 'QPROBE loop-exit kind=[^ ]+ exit=[^ ]+ rounds=[0-9]+ ground=[0-9]+' | join1)
  C_EXITS="${C_EXITS:-none}"
  C_RUNG=$(printf '%s\n' "$raw" | grep -oE 'QPROBE skolemized-egraph\([^)]*\) budget=[^ ]+ elapsed=[^ ]+ result=.*' | join1)
  C_RUNG="${C_RUNG:-none}"
  C_REPLAY=$(printf '%s\n' "$raw" | grep -cE 'QPROBE held-set-replay')
}

run_r() {
  local f="$1" t0 t1 raw rc
  t0=$(date +%s%N)
  raw=$(env AXEYUM_QPROBE=1 AXEYUM_QPROBE_HELD_SET_REPLAY="$REPLAY" \
          timeout $((BUDGET + RHEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  R_V=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  R_V="${R_V:-NONE}"
  R_RC=$rc
  R_MS=$(( (t1 - t0) / 1000000 ))
  R_LINES=$(printf '%s\n' "$raw" | grep -oE 'QPROBE held-set-replay .*' | join1)
  R_LINES="${R_LINES:-none}"
  R_N=$(printf '%s\n' "$raw" | grep -cE 'QPROBE held-set-replay ')
  R_UNSAT=$(printf '%s\n' "$raw" | grep -cE 'QPROBE held-set-replay .* verdict=unsat')
}

printf 'file\tc_verdict\tc_rc\tc_ms\tr_verdict\tr_rc\tr_ms\tr_n\tr_unsat\torder\tstatus\tc_exits\tc_rung\tc_giveup\tr_lines\n' > "$OUT"
i=0
while read -r f; do
  [ -n "$f" ] || continue
  st=$(grep -m1 -oE '\(set-info :status +(sat|unsat|unknown)' "$f" 2>/dev/null \
        | grep -oE '(sat|unsat|unknown)$')
  if [ $((i % 2)) -eq 0 ]; then
    run_c "$f"; run_r "$f"; ord=c-first
  else
    run_r "$f"; run_c "$f"; ord=r-first
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "$C_V" "$C_RC" "$C_MS" "$R_V" "$R_RC" "$R_MS" "$R_N" "$R_UNSAT" \
    "$ord" "${st:-none}" "$C_EXITS" "$C_RUNG" "$C_GIVEUP" "$R_LINES" >> "$OUT"
  i=$((i + 1))
done < "$LIST"
echo "RH-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
