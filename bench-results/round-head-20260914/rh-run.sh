#!/usr/bin/env bash
# Lane ROUND-HEAD: the exit census and the held-set replay, INTERLEAVED per file.
#
# THREE ARMS, ONE BINARY, THREE ENV SETTINGS -- never three builds.
#
#   arm C   (census, 24 s)  AXEYUM_QPROBE=1 AXEYUM_QTRACE=1
#         The shipped run. THE ONLY VERDICT ARM. Gives the seven-way exit
#         census, the route trail, and the `route-open` segment (ADR-1941: the
#         open segment is the discriminator, not `attempts=`).
#
#   arm R1  (replay, 24 s)  + AXEYUM_QPROBE_HELD_SET_REPLAY=<r1_ms>
#                             AXEYUM_QPROBE_HELD_SET_REPLAY_MIN_GROUND=0
#         Replays EVERY discarded/unrefuted ground set at the shipped operating
#         point. In practice this reaches only the EARLY exits -- see the
#         blindness note below.
#
#   arm R2  (replay, <r2_budget> s)  + AXEYUM_QPROBE_HELD_SET_REPLAY=<r2_ms>
#                                      AXEYUM_QPROBE_HELD_SET_REPLAY_MIN_GROUND=<min>
#         A DELIBERATELY MORE GENEROUS OPERATING POINT, disclosed as such. It is
#         not comparable to arm C and its verdict is never differenced against
#         one. Its purpose is that a NEGATIVE under more generous conditions
#         closes the hypothesis harder than a negative at the shipped point.
#
# POLARITY, stated here because copying the wrong runner measures the shipped
# arm against itself and reports a confident zero: the replay is OFF when
# `AXEYUM_QPROBE_HELD_SET_REPLAY` is UNSET, EMPTY, zero, or unparseable. Arm C
# runs it UNSET via `env -u`; arms R1/R2 run it set to a positive integer.
#
# THE BLINDNESS THIS ARM STRUCTURE EXISTS FOR, measured on
# `UFNIA/2019-Preiner/combined/f2_rw160.smt2` before the population was touched:
# that query reaches a discarding exit TWICE. The first holds **11** ground
# terms and fires at the rung's own sub-deadline, 1.5 s into a 24 s query. The
# second holds **1,643** and fires at the instant the root watchdog kills the
# worker thread (`route-open ms=23488 after=q:mbqi-quick`), so an in-process
# replay of it is racing a kill it cannot win -- the probe line never prints.
# An ungated probe also spends its whole allowance on the 11-term set. So R1
# samples the early exits honestly and R2 buys the late ones with a longer
# clock. An instrument that systematically samples the least interesting member
# of a population is worse than none, because its zero reads like a finding.
#
# NEITHER REPLAY ARM IS A VERDICT ARM. Their verdict columns are recorded for
# completeness only; only their `held-set-replay` lines are load-bearing.
#
# All three arms run back to back on the SAME file on the SAME pinned physical
# core, with the arm ORDER ROTATING per file, because ambient load has moved 23
# verdicts in one division at fixed code on these boxes.
#
# Usage: rh-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s] \
#                  [r1_ms] [r2_ms] [r2_min_ground] [r2_budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
R1MS="${7:-3000}"; R2MS="${8:-15000}"; R2MIN="${9:-400}"; R2BUDGET="${10:-60}"
HEADROOM=16
# A replay arm may fire several times per file, each capped at its own budget,
# so the outer kill has to be generous or a slow file reads as a harness failure.
RHEADROOM=240
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

# Collapse a multi-line capture into one TSV cell, `;`-separated, tabs stripped.
join1() { tr '\t' ' ' | tr '\n' ';' | sed 's/;$//'; }

run_c() {
  local f="$1" t0 t1 raw rc rl
  t0=$(date +%s%N)
  raw=$(env -u AXEYUM_QPROBE_HELD_SET_REPLAY -u AXEYUM_QPROBE_HELD_SET_REPLAY_MIN_GROUND \
          AXEYUM_QPROBE=1 AXEYUM_QTRACE=1 \
          timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  C_V=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); C_V="${C_V:-NONE}"
  C_RC=$rc
  C_MS=$(( (t1 - t0) / 1000000 ))
  C_GIVEUP=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
  C_GIVEUP="${C_GIVEUP:-none}"
  C_EXITS=$(printf '%s\n' "$raw" \
    | grep -oE 'QPROBE loop-exit kind=[^ ]+ exit=[^ ]+ rounds=[0-9]+ ground=[0-9]+' | join1)
  C_EXITS="${C_EXITS:-none}"
  C_RUNG=$(printf '%s\n' "$raw" \
    | grep -oE 'QPROBE skolemized-egraph\([^)]*\) budget=[^ ]+ elapsed=[^ ]+ result=.*' | join1)
  C_RUNG="${C_RUNG:-none}"
  # ADR-1936 / ADR-1941: the route fields AND the open segment on every row.
  rl=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*')
  fld() { printf '%s\n' "$rl" | grep -oE "$1=[^ ]+" | head -1 | cut -d= -f2-; }
  C_BOUND=$(fld bound_by);  C_BOUND="${C_BOUND:-na}"
  C_LAST=$(fld last);       C_LAST="${C_LAST:-na}"
  C_BMS=$(fld bound_ms);    C_BMS="${C_BMS:-na}"
  C_TMS=$(fld total_ms);    C_TMS="${C_TMS:-na}"
  C_ATT=$(fld attempts);    C_ATT="${C_ATT:-NOROUTE}"
  local ol
  ol=$(printf '%s\n' "$raw" | grep -m1 -oE 'route-open ms=[0-9]+ after=[^ ]+')
  C_OMS=$(printf '%s\n' "$ol" | grep -oE 'ms=[0-9]+' | head -1 | cut -d= -f2); C_OMS="${C_OMS:-na}"
  C_OAF=$(printf '%s\n' "$ol" | grep -oE 'after=[^ ]+' | head -1 | cut -d= -f2); C_OAF="${C_OAF:-na}"
}

# $1 file, $2 budget_ms, $3 min_ground, $4 solve_budget_s
run_r() {
  local f="$1" ms="$2" min="$3" sb="$4" t0 t1 raw rc
  t0=$(date +%s%N)
  raw=$(env AXEYUM_QPROBE=1 AXEYUM_QPROBE_HELD_SET_REPLAY="$ms" \
          AXEYUM_QPROBE_HELD_SET_REPLAY_MIN_GROUND="$min" \
          timeout $((sb + RHEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((sb * 1000))" \
          "$AX" "$f" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  RV=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); RV="${RV:-NONE}"
  RRC=$rc
  RMS=$(( (t1 - t0) / 1000000 ))
  RLINES=$(printf '%s\n' "$raw" \
    | grep -oE 'QPROBE (held-set-replay[a-z-]*|loop-exit) .*' | join1)
  RLINES="${RLINES:-none}"
  RN=$(printf '%s\n' "$raw" | grep -cE 'QPROBE held-set-replay ')
  RUNSAT=$(printf '%s\n' "$raw" | grep -cE 'QPROBE held-set-replay .* verdict=unsat')
}

printf 'file\tstatus\torder\tc_verdict\tc_rc\tc_ms\tc_bound_by\tc_last\tc_bound_ms\tc_total_ms\tc_attempts\tc_open_ms\tc_open_after\tr1_verdict\tr1_ms\tr1_n\tr1_unsat\tr2_verdict\tr2_ms\tr2_n\tr2_unsat\tc_exits\tc_rung\tc_giveup\tr1_lines\tr2_lines\n' > "$OUT"
i=0
while read -r f; do
  [ -n "$f" ] || continue
  st=$(grep -m1 -oE '\(set-info :status +(sat|unsat|unknown)' "$f" 2>/dev/null \
        | grep -oE '(sat|unsat|unknown)$')
  do_r1() { run_r "$f" "$R1MS" 0 "$BUDGET"; R1V=$RV; R1T=$RMS; R1N=$RN; R1U=$RUNSAT; R1L=$RLINES; }
  do_r2() { run_r "$f" "$R2MS" "$R2MIN" "$R2BUDGET"; R2V=$RV; R2T=$RMS; R2N=$RN; R2U=$RUNSAT; R2L=$RLINES; }
  case $((i % 3)) in
    0) run_c "$f"; do_r1; do_r2; ord=c-r1-r2 ;;
    1) do_r1; do_r2; run_c "$f"; ord=r1-r2-c ;;
    *) do_r2; run_c "$f"; do_r1; ord=r2-c-r1 ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${st:-none}" "$ord" "$C_V" "$C_RC" "$C_MS" \
    "$C_BOUND" "$C_LAST" "$C_BMS" "$C_TMS" "$C_ATT" "$C_OMS" "$C_OAF" \
    "$R1V" "$R1T" "$R1N" "$R1U" "$R2V" "$R2T" "$R2N" "$R2U" \
    "$C_EXITS" "$C_RUNG" "$C_GIVEUP" "$R1L" "$R2L" >> "$OUT"
  i=$((i + 1))
done < "$LIST"
echo "RH-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
