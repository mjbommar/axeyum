#!/usr/bin/env bash
# LRA-MODEL-REPLAY sweep driver.
#
# One pass over a file list with ONE binary and ONE environment, on ONE pinned
# physical core pair. Captures stdout (the verdict), stderr (the `--trace`
# route trail AND this lane's `; LRACENSUS` diagnostic lines), the exit status
# and the wall time.
#
# TIMING. s7's `date` is uutils coreutils and `date +%s%3N` prints NANOseconds
# with the width silently ignored, so every `*_ms` column timed with it on this
# host is off by 10^6. This script uses bash's own $EPOCHREALTIME and
# SELF-CHECKS the unit once per run before any solve: a 200 ms sleep must read
# back between 150 and 400 ms or the script aborts.
#
# Usage: run-sweep.sh <list> <outdir> <cores> <bin> <arm-name> [env assignments...]
set -u
LIST="$1"; OUTDIR="$2"; CORES="$3"; AX="$4"; ARM="$5"; shift 5
BUDGET_S=24
HEADROOM_S=16
VLIM_KB=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

[ -x "$AX" ] || { echo "ABORT: binary $AX missing/not executable"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: list $LIST unreadable"; exit 2; }
mkdir -p "$OUTDIR/cap" || exit 2

AX_SHA=$(sha256sum "$AX" | cut -d' ' -f1)

now_ms() { local s=${EPOCHREALTIME/,/.}; echo "$(( ${s%.*} * 1000 + 10#${s#*.} / 1000 ))"; }

# --- clock unit self-check, before any solve -------------------------------
t0=$(now_ms); sleep 0.2; t1=$(now_ms); d=$((t1 - t0))
if [ "$d" -lt 150 ] || [ "$d" -gt 400 ]; then
  echo "ABORT: clock self-check read ${d} for a 200 ms sleep -- unit is wrong"
  exit 3
fi
echo "clock self-check: 200 ms sleep read ${d} ms  OK"
echo "arm=$ARM cores=$CORES host=$(hostname) binary_sha256=$AX_SHA env: $*"

LEDGER="$OUTDIR/ledger-$ARM.tsv"
printf 'arm\tfile\tverdict\texit\tms\tbinary_sha\tcores\thost\tloadavg\n' > "$LEDGER"

n=0
while read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  slug=$(echo "$rel" | tr '/' '_')
  cap="$OUTDIR/cap/$ARM.$slug"
  load=$(cut -d' ' -f1 /proc/loadavg)
  t0=$(now_ms)
  env "$@" taskset -c "$CORES" \
    timeout -k 5 $((BUDGET_S + HEADROOM_S)) \
    bash -c "ulimit -v $VLIM_KB; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET_S * 1000)) --trace" \
      "$AX" "$CORPUS/$rel" > "$cap.out" 2> "$cap.err"
  rc=$?
  t1=$(now_ms)
  verdict=$(grep -E '^(sat|unsat|unknown)$' "$cap.out" | tail -1)
  [ -n "$verdict" ] || verdict="none"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$ARM" "$rel" "$verdict" "$rc" "$((t1 - t0))" "$AX_SHA" "$CORES" "$(hostname)" "$load" \
    >> "$LEDGER"
done < "$LIST"

echo "arm=$ARM done: $n files -> $LEDGER"
