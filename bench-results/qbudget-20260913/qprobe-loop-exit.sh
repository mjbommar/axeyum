#!/usr/bin/env bash
# WHY A BIGGER BUDGET CAN LOSE A REFUTATION, measured rather than argued.
#
# The instantiation loop's round admission asks whether another round fits WITH
# GROWTH HEADROOM against the REMAINING BUDGET
# (`qinst_egraph.rs:2267-2269`: `remaining < last_round_duration * 8`), and then
# breaks to a FINAL GROUND CHECK over everything it has accumulated. That check's
# own code records the hazard: "the full-set final check over a near-cap
# conjunction is itself a wall (measured 26.7s-then-unknown over 8192
# conjuncts)".
#
# So changing the budget changes the NUMBER OF ROUNDS admitted, hence the SIZE of
# the ground set the final check is handed. A larger ground set is not a better
# one. `AXEYUM_QPROBE=1` prints the line that says both numbers:
#
#   QPROBE loop-exit kind=<exit> exit=<Exit> rounds=<n> ground=<m>
#
# This script prints them per arm, so "the arms reach the final check with
# different accumulated ground" is a measurement and not a story.
#
# Usage: qprobe-loop-exit.sh <bin> <rel-file-list> <cores> [budget_s]
set -u
AX="$1"; LIST="$2"; PIN="$3"; BUDGET="${4:-24}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

# `n_exits` is NOT decoration. The loop runs twice per query (the `q:egraph`
# rung and this retry), and a run killed by its deadline AT A ROUND HEAD returns
# `egraph_timeout()` BEFORE the loop-exit line is printed
# (`qinst_egraph.rs:2256-2258`). So the LAST line printed does not always belong
# to the retry, and a row with fewer lines under one arm than the other is a row
# where one invocation exited silently. Without this column the table invites
# exactly the attribution error it is meant to prevent.
printf 'file\tarm\twall_ms\tverdict\tn_exits\tloop_exit\trounds\tground\n'
while read -r rel; do
  [ -n "$rel" ] || continue
  f="$CORPUS$rel"
  [ -f "$f" ] || { echo "MISSING $rel" >&2; continue; }
  for arm in base ceiling; do
    t0=$(date +%s%N)
    if [ "$arm" = base ]; then
      raw=$(AXEYUM_QPROBE=1 env -u AXEYUM_QINST_EGRAPH_RETRY_SHARE \
              timeout $((BUDGET + 16)) taskset -c "$PIN" \
              bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
              "$AX" "$f" 2>&1)
    else
      raw=$(AXEYUM_QPROBE=1 AXEYUM_QINST_EGRAPH_RETRY_SHARE=1 \
              timeout $((BUDGET + 16)) taskset -c "$PIN" \
              bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
              "$AX" "$f" 2>&1)
    fi
    t1=$(date +%s%N)
    v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
    # The LAST loop-exit line: the loop runs twice per query (the `q:egraph`
    # rung and this retry), and the retry is the one the lever moves.
    n=$(printf '%s\n' "$raw" | grep -cE 'QPROBE loop-exit ')
    le=$(printf '%s\n' "$raw" | grep -oE 'QPROBE loop-exit .*' | tail -1)
    k=$(printf '%s\n' "$le" | grep -oE 'exit=[^ ]+' | head -1 | cut -d= -f2)
    r=$(printf '%s\n' "$le" | grep -oE 'rounds=[0-9]+' | head -1 | cut -d= -f2)
    g=$(printf '%s\n' "$le" | grep -oE 'ground=[0-9]+' | head -1 | cut -d= -f2)
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$rel" "$arm" "$(( (t1 - t0) / 1000000 ))" "${v:-none}" "${n:-0}" \
      "${k:-NO-EXIT-LINE}" "${r:-NO-EXIT-LINE}" "${g:-NO-EXIT-LINE}"
  done
done < "$LIST"
