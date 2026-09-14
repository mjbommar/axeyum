#!/usr/bin/env bash
# ACKPROBE sweep (ADR-2030): for each file, record every consultation of the
# eager Ackermann admission bound -- at which site, in which ORDER, with the
# upstream gate state.
#
# This is a DIAGNOSTIC, not an arm. `AXEYUM_ACKPROBE=1` only prints; the verdict
# is recorded beside it so a probe run that moved a verdict would be visible.
#
# The QUESTION it answers: when `combined.rs:86` hard-declines, had
# `auto.rs:4068` -- the route selector on the SAME constant -- already engaged on
# the same term set? ADR-2020 asserted it had not ("the lazy fallback ... is
# simply not offered to them"). The ordered log is what decides it.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; LOGDIR="$5"; BUDGET="${6:-24}"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$LOGDIR"

printf 'file\tverdict\tms\tauto_engaged\tcombined_refuse\tauto_notengaged\tcombined_admit\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  slug=$(printf '%s' "$f" | tr '/' '_')
  t0=$(date +%s%N)
  v=$(AXEYUM_ACKPROBE=1 timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
        bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
        "$AX" "$CORPUS/$f" 2> "$LOGDIR/$slug.err")
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$v" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  ae=$(grep -c 'site=auto.rs:4068.*engaged=true' "$LOGDIR/$slug.err" || true)
  an=$(grep -c 'site=auto.rs:4068.*engaged=false' "$LOGDIR/$slug.err" || true)
  cr=$(grep -c 'site=combined.rs:86.*verdict=refuse' "$LOGDIR/$slug.err" || true)
  ca=$(grep -c 'site=combined.rs:86.*verdict=admit' "$LOGDIR/$slug.err" || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$v" "$(( (t1 - t0) / 1000000 ))" \
    "$ae" "$cr" "$an" "$ca" >> "$OUT"
  echo "done $f -> $v auto_engaged=$ae combined_refuse=$cr"
done < "$LIST"
echo "DONE $OUT"
