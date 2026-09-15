#!/usr/bin/env bash
# SILENT-HANG -- get a STACK, not a hypothesis.
#
# `stack-sample.sh` tried gdb for the caller chain and CANNOT WORK ON THIS HOST:
# `/proc/sys/kernel/yama/ptrace_scope` is `1`, which permits a ptrace attach
# only from an ANCESTOR, and the sampler's gdb is a SIBLING of the solver.  All
# four attempts returned "Could not attach to process" (`prof/havoc-sum/bt.txt`
# keeps the receipts).  That is recorded rather than quietly dropped, because an
# empty `bt.txt` read as "no stack available" would be exactly the absence-as-
# finding this lane exists to refuse.
#
# So: frame pointers instead (`build-fp.sh`), and `perf --call-graph=fp`, which
# needs no ptrace and gives an exact caller chain.
#
#   perf-fp.sh <file> <tag> <pin> [budget_s]
#
# Alongside the profile it samples `/proc` once a second.  That is the channel
# that answers the question the watchdog cannot (R6):
#   worker_state   `R` is on CPU, `S`/`D` is blocked -- a deadline passing says
#                  nothing about which
#   utime_ticks    climbing at ~100/s is 100 % of one core; flat is not running
#   rss_kb         flat is a fixed working set; climbing is the memory a
#                  wall-clock timeout does not bound
set -u
W="$(cd "$(dirname "$0")" && pwd)"
F="$1"; TAG="$2"; PIN="${3:-8}"; BUDGET="${4:-60}"
CORPUS="${SH_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SH_AX_FP:-/nas3/data/axeyum/harness/silent-hang/bin/smtcomp_cli-fp}"
OUT="$W/prof/$TAG"
[ -x "$AX" ] || { echo "ABORT: $AX missing -- run build-fp.sh"; exit 2; }
[ -r "$CORPUS/$F" ] || { echo "ABORT: $CORPUS/$F missing"; exit 2; }
mkdir -p "$OUT"
printf 'sec\trss_kb\tvmhwm_kb\tworker_utime_ticks\tworker_state\n' > "$OUT/proc.tsv"

AXEYUM_TRACE=1 taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms $((BUDGET * 1000)) \
  > "$OUT/stdout.txt" 2>&1 &
PID=$!
worker=""
for _ in $(seq 1 100); do
  for t in /proc/$PID/task/*; do
    tid=$(basename "$t"); [ "$tid" = "$PID" ] && continue; worker=$tid; break
  done
  [ -n "$worker" ] && break
  sleep 0.1
done
[ -n "$worker" ] || worker=$PID
echo "pid=$PID worker_tid=$worker file=$F"

# `-m 256` is NOT cosmetic.  With five of these running at once and the default
# mmap size, two of five died with "Permission error mapping pages" against
# `perf_event_mlock_kb` and wrote a perf.data with NO samples -- which reports
# as an empty profile, i.e. exactly the absence-read-as-a-finding this lane is
# about.  `--sample-count` is checked after the run instead of trusted.
timeout $((BUDGET + 10)) perf record -F 299 -g --call-graph=fp -m ${PERF_MMAP:-32} -o "$OUT/perf.data" \
  -p "$PID" > "$OUT/perf.log" 2>&1 &
PERFPID=$!

sec=0
while kill -0 "$PID" 2>/dev/null && [ "$sec" -lt "$((BUDGET + 8))" ]; do
  printf '%s\t%s\t%s\t%s\t%s\n' "$sec" \
    "$(awk '/^VmRSS:/{print $2}' /proc/$PID/status 2>/dev/null)" \
    "$(awk '/^VmHWM:/{print $2}' /proc/$PID/status 2>/dev/null)" \
    "$(awk '{print $14}' /proc/$PID/task/$worker/stat 2>/dev/null)" \
    "$(awk '{print $3}' /proc/$PID/task/$worker/stat 2>/dev/null)" >> "$OUT/proc.tsv"
  sleep 1; sec=$((sec + 1))
done
wait "$PID" 2>/dev/null; rc=$?
wait "$PERFPID" 2>/dev/null || true

# The caller chain, folded, top 12.  `--no-children` so a frame's own cost is
# its own, and `-g folded` so the chain is on one line and greppable.
# An empty profile must never be readable as "nothing was running".  perf's own
# sample count decides whether this profile is evidence at all.
#
# The FIRST version of this guard read `nr_samples` out of `--header-only`.
# That field does not exist in this perf's header, so the guard printed
# "samples: 0" over a profile whose top frame was 54 % -- a checker that
# manufactures a false alarm is the same defect class as one that cannot fail,
# and it is recorded here rather than quietly corrected.  `# Samples:` in the
# report body is the field that exists.
NSAMP=$(perf report -i "$OUT/perf.data" --stdio 2>/dev/null \
          | grep -m1 '^# Samples:' | sed 's/.*: *//')
{
  echo "### file: $F"
  echo "### rc=$rc  (R7: exit status is its own channel)"
  echo "### perf samples: ${NSAMP:-0}  -- ZERO means THE PROFILER FAILED, not that nothing ran"
  echo "### leaf self-cost"
  perf report -i "$OUT/perf.data" --no-children --stdio --percent-limit 1 2>/dev/null \
    | grep -E '^ +[0-9]+\.[0-9]+%' | head -12
  echo "### caller chains (folded)"
  perf report -i "$OUT/perf.data" --no-children --stdio -g folded --percent-limit 3 2>/dev/null \
    | grep -E '^ +[0-9]+\.[0-9]+%|^ +[0-9]+\.[0-9]+ ' | head -40
} > "$OUT/profile.txt" 2>&1
echo "PROFILED $OUT rc=$rc"
tail -n +1 "$OUT/profile.txt" | head -20
