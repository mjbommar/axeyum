#!/usr/bin/env bash
# SILENT-HANG -- get a STACK, not a hypothesis.
#
# The bucket is defined by the absence of an instrument reading, so the only
# way to say what the worker is doing is to ask the operating system while it
# is still doing it.  Two independent samplers, because each has a failure mode
# the other does not:
#
#   gdb   `thread apply all bt` names the WHOLE call chain including the
#         caller, which is the part that says WHICH pre-route stage this is.
#         It stops the process to do it, so it perturbs timing -- fine, since
#         the question is "what", not "how fast".
#   perf  a free-running sample, no stop, so it says where the time is
#         CONCENTRATED rather than where one instant happened to land.
#         Its DWARF unwinder truncates on this binary's 512 MiB worker stack,
#         so its leaf symbols are trustworthy and its callers are not -- which
#         is exactly the half gdb supplies.
#
# Neither is believed alone.  A frame named by gdb at several independent
# instants AND carrying perf's leaf symbol is the finding.
#
#   stack-sample.sh <file> <tag> <pin> [budget_s] [n_backtraces]
set -u
W="$(cd "$(dirname "$0")" && pwd)"
F="$1"; TAG="$2"; PIN="${3:-2}"; BUDGET="${4:-120}"; NBT="${5:-6}"
CORPUS="${SH_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SH_AX:-/nas3/data/axeyum/harness/silent-hang/bin/smtcomp_cli-sh}"
OUT="$W/prof/$TAG"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$CORPUS/$F" ] || { echo "ABORT: $CORPUS/$F missing"; exit 2; }
mkdir -p "$OUT"
: > "$OUT/bt.txt"; : > "$OUT/rss.tsv"; printf 'sec\trss_kb\tvmhwm_kb\tworker_utime_ticks\tworker_state\n' > "$OUT/rss.tsv"

AXEYUM_TRACE=1 taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms $((BUDGET * 1000)) \
  > "$OUT/stdout.txt" 2>&1 &
PID=$!
echo "pid=$PID file=$F budget=${BUDGET}s"

# The worker is the second thread: the harness spawns exactly one.  Wait for it
# rather than assuming, and report if it never appears.
worker=""
for _ in $(seq 1 100); do
  for t in /proc/$PID/task/*; do
    tid=$(basename "$t")
    [ "$tid" = "$PID" ] && continue
    worker=$tid; break
  done
  [ -n "$worker" ] && break
  sleep 0.1
done
[ -n "$worker" ] || { echo "NOTE: no second thread appeared -- the solve ran on the main thread"; worker=$PID; }
echo "worker_tid=$worker"

# perf over the whole run, free-running.
timeout $((BUDGET + 10)) perf record -F 199 -g -o "$OUT/perf.data" -p "$PID" \
  > "$OUT/perf.log" 2>&1 &
PERFPID=$!

# gdb backtraces at spread instants + a /proc sample every second.  The /proc
# sampler is what answers R6's (a)-vs-(c): `worker_utime_ticks` climbing at ~100
# per second is a thread ON CPU, a flat one is a thread BLOCKED, and `vmhwm_kb`
# is the peak a wall-clock timeout does not bound.
step=$(( BUDGET / (NBT + 1) )); [ "$step" -lt 3 ] && step=3
next=$step; sec=0
while kill -0 "$PID" 2>/dev/null && [ "$sec" -lt "$((BUDGET + 5))" ]; do
  rss=$(awk '/^VmRSS:/{print $2}' /proc/$PID/status 2>/dev/null)
  hwm=$(awk '/^VmHWM:/{print $2}' /proc/$PID/status 2>/dev/null)
  ut=$(awk '{print $14}' /proc/$PID/task/$worker/stat 2>/dev/null)
  st=$(awk '{print $3}' /proc/$PID/task/$worker/stat 2>/dev/null)
  printf '%s\t%s\t%s\t%s\t%s\n' "$sec" "${rss:-na}" "${hwm:-na}" "${ut:-na}" "${st:-na}" >> "$OUT/rss.tsv"
  if [ "$sec" -ge "$next" ]; then
    {
      echo "===== backtrace at t=${sec}s ====="
      timeout 60 gdb -p "$PID" -batch \
        -ex 'set pagination off' -ex 'set print frame-arguments none' \
        -ex 'thread apply all bt 45' 2>&1 | grep -vE '^\[|^Reading|^Downloading|^warning:|^Missing'
    } >> "$OUT/bt.txt"
    next=$((next + step))
  fi
  sleep 1
  sec=$((sec + 1))
done
wait "$PID" 2>/dev/null; rc=$?
wait "$PERFPID" 2>/dev/null || true
echo "rc=$rc" >> "$OUT/stdout.txt"
echo "SAMPLED $OUT (rc=$rc)"
grep -cE '^=====' "$OUT/bt.txt" | sed 's/^/backtraces: /'
