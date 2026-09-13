#!/usr/bin/env bash
# ANSWERS THE STARVATION QUESTION WITH A MEASUREMENT, not with a truncated trace.
#
# The census qtrace reads `egraph@24.017:declined;(+23 segments of other stages
# dropped)`, and that `(+N dropped)` is a RENDERING limit on the trace string.
# It says nothing about whether those stages ran for microseconds, ran fully and
# declined, or never started. `AXEYUM_QPROBE=1` prints the rung-entry lines that
# do say:
#
#   [mbqi-rung] state=... budget_ms=...        the first-refusal MBQI rung
#   [mbqi-shape] exit=... ...                  WHICH guard sent MBQI to e-matching
#   QPROBE skolemized-egraph(<label>) budget=... elapsed=... result=...
#                                              the SECOND e-graph pass, its
#                                              granted budget and what it spent
#
# So this prints, per file: what the retry was GRANTED, what it SPENT, and what
# the whole run's wall clock was -- which is the difference between "the ladder
# ran out of clock" and "the ladder ran out of RUNGS with clock left over".
#
# Usage: qprobe-budgets.sh <bin> <rel-file-list> <cores> [arm-env-value] [budget_s]
#   arm-env-value: omit or "-" for the base arm (env -u), "1" for the ceiling.
set -u
AX="$1"; LIST="$2"; PIN="$3"; ARM="${4:--}"; BUDGET="${5:-24}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'file\twall_ms\tverdict\tmbqi_rung\tmbqi_shape_exit\tretry_budget\tretry_elapsed\tretry_result\n'
while read -r rel; do
  [ -n "$rel" ] || continue
  f="$CORPUS$rel"
  [ -f "$f" ] || { echo "MISSING $rel" >&2; continue; }
  t0=$(date +%s%N)
  if [ "$ARM" = "-" ]; then
    raw=$(AXEYUM_QPROBE=1 env -u AXEYUM_QINST_EGRAPH_RETRY_SHARE \
            timeout $((BUDGET + 16)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>&1)
  else
    raw=$(AXEYUM_QPROBE=1 AXEYUM_QINST_EGRAPH_RETRY_SHARE="$ARM" \
            timeout $((BUDGET + 16)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>&1)
  fi
  t1=$(date +%s%N)
  wall=$(( (t1 - t0) / 1000000 ))
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  rung=$(printf '%s\n' "$raw" | grep -m1 -oE '\[mbqi-rung\] state=[^ ]+ budget_ms=[-0-9]+' \
           | sed 's/\[mbqi-rung\] //' | tr ' ' ',')
  shape=$(printf '%s\n' "$raw" | grep -m1 -oE '\[mbqi-shape\] exit=[^ ]+' | cut -d= -f2)
  # The LAST skolemized-egraph line: `prove_unsat_by_ematching` has two call
  # sites ("residual" and "exhausted") and only one of them runs per query.
  sk=$(printf '%s\n' "$raw" | grep -oE 'QPROBE skolemized-egraph\(.*' | tail -1)
  sb=$(printf '%s\n' "$sk" | grep -oE 'budget=[^ ]+' | cut -d= -f2-)
  se=$(printf '%s\n' "$sk" | grep -oE 'elapsed=[^ ]+' | cut -d= -f2-)
  sr=$(printf '%s\n' "$sk" | sed -E 's/.*result=//' | tr '\t' ' ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$wall" "${v:-none}" "${rung:-none}" "${shape:-none}" \
    "${sb:-NEVER-RAN}" "${se:-NEVER-RAN}" "${sr:-NEVER-RAN}"
done < "$LIST"
