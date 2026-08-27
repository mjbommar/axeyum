#!/usr/bin/env bash
# Measure what the gate-admission change does to a starved gate, under a
# CONTROLLED, REPRODUCIBLE offered load.
#
# Why not a real battery A/B: a contended battery costs ~35 minutes, the honest
# comparison needs the SAME offered load on both sides (which a shared box with
# live lanes cannot provide), and `hooks/pre-push` only runs on a push --
# starting one would perturb the very thing being measured and block every other
# lane behind the gate flock. So the load is generated here, identically for
# both arms.
#
# What this establishes: the scheduling change, on this host, under an offered
# load calibrated to the observed one. What it does NOT establish: an end-to-end
# battery number. Stated rather than implied -- see
# docs/research/11-design-review/2026-08-27-gate-throughput.md.
#
# Three arms, identical fixed work in each:
#   quiet    subject alone
#   before   subject vs load, both at nice 0     (the shipped behaviour)
#   after    subject at nice 0, load at nice 10  (this change)
#
# TWO EARLIER VERSIONS OF THIS SCRIPT PRODUCED WRONG ANSWERS, both of which
# looked plausible, and both are guarded against below:
#
#   1. Threaded burners measured 1.11x inflation where the gate sees 4-7x.
#      Python holds the GIL through a 32-byte sha256, so each "4-thread" burner
#      pinned ONE core. Everything here forks PROCESSES.
#   2. The arms were not comparable -- load 14.3 vs 31.6 -- because killing the
#      wrapper leaves its FORKED CHILDREN orphaned, so the second arm ran on top
#      of the first arm's load. Confirmed by `ps`: nice-10 spinners from arm one
#      were still at 97% CPU during arm two. Children now exit when reparented,
#      each arm waits for the process count to return to baseline, and the arms
#      are REPORTED and compared -- so a contaminated run says NOT COMPARABLE
#      instead of printing a confident wrong ratio.
#
# Usage: scripts/measure-gate-admission.sh [iterations-per-subject-process]
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

JOBS="${AXEYUM_MEASURE_JOBS:-5}"          # concurrent "lanes" (= the slot count)
PROCS="${AXEYUM_MEASURE_PROCS:-16}"       # busy processes per lane job
SUBJ="${AXEYUM_MEASURE_SUBJ:-$(nproc)}"   # subject width = a cargo test binary's
WORK="${1:-${AXEYUM_MEASURE_WORK:-12000000}}"

# Children exit when their parent dies, so an arm cannot leak load into the next
# one. `signal.alarm` is the backstop: nothing spawned here can outlive 75 s and
# become the kind of orphan CLAUDE.md records at 85 hours and 99.5% CPU.
TOKEN="axeyum-measure-$$-$(date +%s)"
burner_prog='
import hashlib, os, signal, sys, time
# argv[2] is a unique token; see reap_burners.
for _ in range(int(sys.argv[1])):
    if os.fork() == 0:
        signal.alarm(45)
        h = b"y"; i = 0
        while True:
            h = hashlib.sha256(h).digest(); i += 1
            if i % 20000 == 0 and os.getppid() == 1:
                os._exit(0)
signal.alarm(50)
time.sleep(50)
'

# The subject models a `cargo test` binary: SUBJ worker processes, fixed work
# each, wall time is when the last finishes. It must be parallel, because that
# is what makes the observed inflation as large as it is -- a 16-thread binary
# against 80 lane threads gets a sixteenth of the box, not half of it.
subject_prog='
import hashlib, os, sys
n = int(sys.argv[1]); procs = int(sys.argv[2]); kids = []
for _ in range(procs):
    pid = os.fork()
    if pid == 0:
        h = b"x"
        for _ in range(n):
            h = hashlib.sha256(h).digest()
        os._exit(0)
    kids.append(pid)
for k in kids:
    os.waitpid(k, 0)
'

busy() { pgrep -c -x python3 2>/dev/null || echo 0; }

# The MODE nice of the processes pgrep actually matched.
#
# NOT `ps -C python3`: measured on this host, that flag did not filter at all --
# it printed every process on the box, so an earlier run of this script reported
# the competitors as "nice 19" when 19 was `khugepaged`. Both arms then showed
# the same value and the change looked inert. An instrument that answers a
# question you did not ask is indistinguishable from a strong negative result.
competitor_nice() {
  local pids
  pids="$(pgrep -x python3 2>/dev/null | tr '\n' ',' | sed 's/,$//')"
  [ -n "$pids" ] || { echo "n/a"; return; }
  ps -o ni= -p "$pids" 2>/dev/null | tr -d ' ' | sort -n | uniq -c | sort -rn |
    head -1 | awk '{print $2}'
}

# REFUSE TO RUN WHILE A PUSH BATTERY IS LIVE, for two independent reasons.
#
# Measurement: a battery saturates this box, so the arms are offered different
# loads and the comparison is meaningless. An earlier run of this script was
# confounded exactly this way -- `hooks/pre-push` was resident with rustc at
# 100%, and the arms came out 69 vs 85 competitors.
#
# Courtesy, which matters more: this script deliberately oversubscribes 16 cores
# for ~40 s. Doing that to somebody else's gate is precisely the harm the change
# it is measuring exists to remove. AXEYUM_MEASURE_FORCE=1 overrides.
if [ "${AXEYUM_MEASURE_FORCE:-0}" != "1" ] \
   && [ "$(pgrep -c -f 'hooks/pre-push' 2>/dev/null || echo 0)" -gt 0 ]; then
  echo "measure-gate-admission: a pre-push battery is running on this host." >&2
  echo "  Refusing: the arms would be offered different loads, AND generating" >&2
  echo "  40 s of deliberate oversubscription against another lane's gate is" >&2
  echo "  the exact harm this change exists to remove." >&2
  echo "  Re-run when it has finished, or AXEYUM_MEASURE_FORCE=1 to override." >&2
  exit 75
fi
BASE="$(busy)"

time_subject() {
  local start end
  start=$(date +%s.%N)
  python3 -c "$subject_prog" "$WORK" "$SUBJ" >/dev/null 2>&1
  end=$(date +%s.%N)
  awk -v a="$start" -v b="$end" 'BEGIN{printf "%.1f", b-a}'
}

pids=()
start_load() {
  local i want
  for i in $(seq 1 "$JOBS"); do
    env "$@" AXEYUM_CARGO_BIN=python3 \
      scripts/cargo-serialized.sh -c "$burner_prog" "$PROCS" "$TOKEN" >/dev/null 2>&1 &
    pids+=("$!")
  done
  want=$((BASE + JOBS * PROCS))
  for _ in $(seq 1 20); do
    [ "$(busy)" -ge "$want" ] && break
    sleep 1
  done
}

# Resolve the token to PIDs, drop our own, kill the rest by PID.
reap_burners() {
  local victims p
  victims="$(pgrep -f "$TOKEN" 2>/dev/null | grep -vx "$$" || true)"
  for p in $victims; do
    [ "$p" = "$$" ] && continue
    kill -9 "$p" 2>/dev/null
  done
}

stop_load() {
  local p
  # By PID, never `pkill -f <pattern>`: CLAUDE.md records a lane whose pattern
  # matched its own launcher and killed it.
  for p in ${pids[@]+"${pids[@]}"}; do
    kill "$p" 2>/dev/null
  done
  wait 2>/dev/null
  pids=()
  reap_burners
  # Wait for the FORKED CHILDREN to notice, not just for the wrappers to exit.
  # This is the guard for failure mode 2 in the header.
  for _ in $(seq 1 40); do
    [ "$(busy)" -le "$((BASE + 2))" ] && break
    sleep 1
  done
}
trap 'stop_load' EXIT

echo "host=$(uname -n) cores=$(nproc) slots=$(scripts/cargo-serialized.sh --slots)"
echo "work=$WORK/proc  subject_width=$SUBJ  load=${JOBS}x${PROCS} procs"
echo "baseline python3 procs on this host: $BASE"
echo

quiet="$(time_subject)"
printf 'QUIET   competitors=%-4s  %ss\n' 0 "$quiet"

start_load AXEYUM_CARGO_NICE=0 AXEYUM_CARGO_CPUWEIGHT=0
b_busy="$(busy)"
b_nice="$(competitor_nice)"
before="$(time_subject)"
printf 'BEFORE  competitors=%-4s  %ss   (competitor nice=%s)\n' \
  "$((b_busy - BASE))" "$before" "$b_nice"
stop_load

start_load AXEYUM_CARGO_NICE=10 AXEYUM_CARGO_CPUWEIGHT=10
a_busy="$(busy)"
a_nice="$(competitor_nice)"
after="$(time_subject)"
printf 'AFTER   competitors=%-4s  %ss   (competitor nice=%s)\n' \
  "$((a_busy - BASE))" "$after" "$a_nice"
stop_load

echo
# The arms are only comparable if they were offered the same load. Assert it
# rather than leaving the reader to trust it: the previous version of this
# script silently compared 14.3 against 31.6 and reported the ratio anyway.
awk -v q="$quiet" -v b="$before" -v a="$after" \
    -v bb="$((b_busy - BASE))" -v ab="$((a_busy - BASE))" \
    -v bn="$b_nice" -v an="$a_nice" 'BEGIN{
  d = bb > ab ? bb - ab : ab - bb;
  ok = (bb > 0 && ab > 0 && d * 10 <= bb) ? "COMPARABLE" : "NOT COMPARABLE";
  printf "arms: before=%d competitors (nice %s), after=%d (nice %s)  -> %s\n",
         bb, bn, ab, an, ok;
  if (ok == "NOT COMPARABLE") {
    print "  offered load differed by more than 10%; do not quote the ratio.";
    exit 1;
  }
  if (bn == an) {
    print "  both arms ran at the SAME nice level; the wrapper is not applying it.";
    exit 1;
  }
  printf "inflation BEFORE: %.2fx quiet\n", b/q;
  printf "inflation AFTER : %.2fx quiet\n", a/q;
  printf "gate speedup under the SAME offered load: %.2fx\n", b/a;
}'
