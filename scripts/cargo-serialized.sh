#!/usr/bin/env bash
# One heavy cargo job at a time on this host, with a memory ceiling.
#
# Why this exists, measured rather than feared: concurrent cargo invocations
# from parallel lanes have taken down this fleet's dev boxes twice (s1 and s4),
# and on 2026-08-17 a kernel OOM killed a live agent session -- one test reached
# 125 GB because `recv_timeout` on a detached thread bounds *time*, not memory.
# Nothing in the repository stopped a second lane from starting a build while
# the first was resident; every lane was told to "serialize" in prose, and prose
# does not hold a lock.
#
# So: an flock on a host-local file (NOT in the repo -- worktrees differ, the
# RAM matters per host) plus a systemd scope carrying MemoryMax AND
# MemorySwapMax. If the scope hits the ceiling the JOB dies; without it the
# host's OOM killer picks, and it has picked the agent.
#
# MemoryMax ALONE DOES NOT BITE, and I nearly shipped the claim that it does.
# Measured on this box: `MemoryMax=64M` applies (`memory.max` reads 67108864 in
# the scope's cgroup) and a 400 MB allocation still SUCCEEDS, because
# `memory.swap.max` is `max` and the cgroup simply swaps. This host has 7 G of
# swap with 6 G already in use, so a runaway test does not get capped -- it
# thrashes and then takes the box down anyway, which is the failure this script
# exists to prevent. Adding `MemorySwapMax=0` changes the same allocation to
# status **137** (SIGKILL by the cgroup's own OOM killer) with the host
# untouched. Ceiling without swap ceiling is decoration.
#
# ONE AT A TIME WAS TOO STRICT, MEASURED. On 2026-08-18 with seven lanes active
# this box sat at load 3.13 with 105 GB free and THREE jobs blocked on the lock.
# The hazard the lock was built for is memory, not CPU -- and MemoryMax +
# MemorySwapMax already bound that per job. So the lock is now a counting
# semaphore of N slots, N derived from RAM / the per-job ceiling, and a single
# runaway is still capped by its own cgroup rather than by everyone else waiting.
#
# THE SLOTS BOUND MEMORY AND NOTHING BOUNDS CPU, which is a different problem
# and it is now the binding one. Measured 2026-08-27 (see
# docs/research/11-design-review/2026-08-27-gate-throughput.md): five slots x
# `nproc`-wide rustc and test threads is a 5x oversubscription of a 16-core box,
# and `hooks/pre-push` -- the authoritative pre-merge gate -- was one of six
# EQUAL consumers competing for it. Load reached 17.7/16 and the battery went
# from ~250 s to 2,152 s, uniformly inflated across every step: starvation, not
# a regression in any one gate.
#
# The fix is PRIORITY, not tighter admission. Capping each job's `-j` would make
# a lone job N times slower on an idle box, and blocking lanes destroys the
# parallelism that produces the work in the first place. `nice` costs nothing
# when the box is quiet (a lone job still gets all 16 cores) and only bites when
# it is oversubscribed -- which is exactly the condition being fixed. So lane
# work runs at AXEYUM_CARGO_NICE (default 10) and the push battery runs at 0.
#
# Usage:
#   scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full
#   scripts/cargo-serialized.sh --self-check   # does the ceiling actually bite HERE?
#   scripts/cargo-serialized.sh --slots        # print the computed slot count
#   scripts/cargo-serialized.sh --batch <cmd...>  # one slot for a whole gate
#   AXEYUM_CARGO_MEM=48G scripts/cargo-serialized.sh test --workspace --all-features
#
# Env:
#   AXEYUM_CARGO_SLOTS concurrent jobs on this host (default: RAM / MEM, 1..6)
#   AXEYUM_CARGO_MEM   scope MemoryMax          (default 24G)
#   AXEYUM_CARGO_SWAP  scope MemorySwapMax      (default 0 -- see above)
#   AXEYUM_CARGO_WAIT  seconds to wait for lock (default 5400; 0 = fail fast)
#   AXEYUM_CARGO_CPUS  taskset list             (default unset -- no pinning)
#   AXEYUM_CARGO_NICE  nice(1) increment        (default 10; 0 = no nice/ionice)
#   AXEYUM_CARGO_CPUWEIGHT  scope CPUWeight     (default 10 vs systemd's 100;
#                                                0 = do not set it)
#
# Exit status is the cargo job's, unchanged, EXCEPT 75 (EX_TEMPFAIL) when the
# lock could not be taken in time -- distinguishable from a test failure, which
# is the whole point of not just returning 1.
set -uo pipefail

LOCK="${AXEYUM_CARGO_LOCK:-/var/tmp/axeyum-cargo.lock}"

# Slots: floor(RAM_GB / MEM_GB), clamped to [1, 6]. The clamp is not timidity --
# beyond a handful of concurrent cargo jobs this workspace is I/O and link bound,
# and the ceiling keeps the worst case (every slot at MemoryMax) inside RAM.
slots_default() {
  local ram mem
  ram=$(awk '/MemTotal/{print int($2/1048576)}' /proc/meminfo 2>/dev/null) || ram=8
  mem="${AXEYUM_CARGO_MEM:-24G}"
  mem=${mem%[Gg]}
  case "$mem" in ''|*[!0-9]*) mem=24 ;; esac
  local n=$(( ram / mem ))
  [ "$n" -lt 1 ] && n=1
  [ "$n" -gt 6 ] && n=6
  echo "$n"
}
SLOTS="${AXEYUM_CARGO_SLOTS:-$(slots_default)}"
MEM="${AXEYUM_CARGO_MEM:-24G}"
SWAP="${AXEYUM_CARGO_SWAP:-0}"
WAIT="${AXEYUM_CARGO_WAIT:-5400}"
NICE="${AXEYUM_CARGO_NICE:-10}"
CPUW="${AXEYUM_CARGO_CPUWEIGHT:-10}"

if [ "$#" -eq 0 ]; then
  echo "usage: $0 <cargo args...>   |   $0 --batch <cmd...>   |   $0 --self-check" >&2
  exit 2
fi

# `--slots` prints what this host would admit, with no side effects. It exists
# so a control can assert the arithmetic without re-deriving it, and so an agent
# can see the number rather than infer it: CLAUDE.md and several docs still say
# "one cargo at a time", which stopped being true on 2026-08-18.
if [ "$1" = "--slots" ]; then
  echo "$SLOTS"
  exit 0
fi

# BATCH MODE: one slot for an entire gate, not one per cargo invocation.
#
# `scripts/check.sh` fires ~100 bare `cargo` calls. Wrapping each would take and
# drop 100 slots and still let 5 aggregate gates run at once; wrapping the whole
# script takes ONE slot for the run and holds it. The nested calls see
# AXEYUM_CARGO_SLOT_HELD and skip the slot (see below), so this cannot deadlock
# against itself -- which is the failure a naive "wrap everything" would produce
# the moment a wrapped script called a wrapped script.
#
# Deliberately NO memory scope here: a batch is a SUPERVISOR, not a cargo job.
# Putting `MemoryMax=24G` on `check.sh` would have the cgroup SIGKILL the whole
# aggregate gate at a threshold none of its steps individually exceeded, and the
# gate would report a failure that is not a failure -- the "checker that cannot
# fail" defect inverted, which is just as bad. The nested cargo jobs each still
# get their own scope, so the ceiling that actually matters is unchanged.
BATCH=0
if [ "$1" = "--batch" ]; then
  BATCH=1
  shift
  if [ "$#" -eq 0 ]; then
    echo "usage: $0 --batch <cmd...>" >&2
    exit 2
  fi
fi

# `--self-check` runs a deliberate over-allocation through the SAME lock and the
# SAME scope construction as a real job, and fails if it survives. It exists
# because the ceiling silently did not bite until `MemorySwapMax` was added, and
# a config that looks applied is exactly what this repository keeps getting
# caught by. Per-host, because swap and delegation differ per host: a wrapper
# that capped s4 says nothing about s5.
if [ "$1" = "--self-check" ]; then
  probe='b = bytearray(400 * 1024 * 1024); print("SURVIVED")'
  out=$(AXEYUM_CARGO_MEM=64M AXEYUM_CARGO_BIN=python3 \
        AXEYUM_CARGO_LOCK="${LOCK}.self-check" \
        "$0" -c "$probe" 2>&1)
  status=$?
  host=$(uname -n)
  if [ "$status" = "137" ]; then
    echo "CARGO_SERIALIZED_SELF_CHECK|host=$host|verdict=enforced|status=137 (cgroup SIGKILL)"
    exit 0
  fi
  echo "CARGO_SERIALIZED_SELF_CHECK|host=$host|verdict=NOT-ENFORCED|status=$status|out=$out" >&2
  echo "  A 400 MB allocation under MemoryMax=64M was not killed. The ceiling on this" >&2
  echo "  host is decoration: a runaway job will reach the HOST OOM killer, which on" >&2
  echo "  this fleet has killed the agent rather than the job. Check that the user" >&2
  echo "  systemd manager delegates 'memory' (cgroup.controllers) and that" >&2
  echo "  MemorySwapMax is being applied (memory.swap.max in the scope's cgroup)." >&2
  exit 1
fi

touch "$LOCK" 2>/dev/null || LOCK="${TMPDIR:-/tmp}/axeyum-cargo.lock"

# `AXEYUM_CARGO_BIN` exists so `--self-check` can drive this exact path with a
# probe instead of cargo. Nothing else should set it.
if [ "$BATCH" = "1" ]; then
  run=("$@")
else
  run=("${AXEYUM_CARGO_BIN:-cargo}" "$@")
fi
if [ -n "${AXEYUM_CARGO_CPUS:-}" ]; then
  run=(taskset -c "$AXEYUM_CARGO_CPUS" "${run[@]}")
fi
# `--scope` runs it as a child of THIS shell's cgroup rather than a transient
# service, so stdout/stderr and the exit status pass through unchanged. Without
# a working user manager (a bare ssh session may have none) fall back to running
# it directly: the lock is still worth having even when the ceiling is not.
if [ "$BATCH" = "1" ]; then
  : # a supervisor, not a cargo job -- see the --batch comment above
elif systemctl --user show-environment >/dev/null 2>&1; then
  scope=(systemd-run --user --scope -q
         -p "MemoryMax=$MEM" -p "MemorySwapMax=$SWAP")
  # The knob that actually crosses a session boundary -- see the header. The
  # slice property is set here rather than shipped as a unit file so the wrapper
  # stays self-contained; it is idempotent and costs a few milliseconds.
  if [ "$CPUW" != "0" ]; then
    systemctl --user set-property axeyumlane.slice "CPUWeight=$CPUW" \
      >/dev/null 2>&1 || true
    scope+=(--slice=axeyumlane -p "CPUWeight=$CPUW")
  fi
  run=("${scope[@]}" "${run[@]}")
else
  echo "cargo-serialized: no user systemd manager; running WITHOUT MemoryMax=$MEM" >&2
fi

# PRIORITY. `nice` is applied OUTSIDE the systemd scope so it covers the scope
# and every descendant, and `ionice -c 3` (idle) because a cold workspace build
# is I/O bound as often as it is CPU bound -- 246 lane worktrees each building
# their own `target/` is 363 GB of write traffic that the push battery competes
# with for the same disk.
#
# `AXEYUM_CARGO_NICE=0` disables both, and that is what `hooks/pre-push` sets:
# the gate is latency-sensitive interactive work with a human (or a stalled
# lane) waiting on it, while lane builds are throughput work that does not care
# about a few minutes. Renicing DOWN is unprivileged; renicing UP is not, which
# is why this yields the lanes rather than promoting the battery.
if [ "$NICE" != "0" ] && command -v nice >/dev/null 2>&1; then
  run=(nice -n "$NICE" "${run[@]}")
  if command -v ionice >/dev/null 2>&1; then
    run=(ionice -c 3 "${run[@]}")
  fi
fi

# RE-ENTRANCY. A job that is already inside somebody's slot must not take a
# second one, or a wrapped script calling a wrapped script deadlocks the moment
# the slots run out -- and it would deadlock silently, as a 5,400 s wait.
# The marker is exported below for the children of a slot we actually took.
if [ "${AXEYUM_CARGO_SLOT_HELD:-0}" = "1" ]; then
  exec "${run[@]}"
fi
export AXEYUM_CARGO_SLOT_HELD=1

# Take ANY free slot, and keep looking at every slot until one frees or WAIT
# expires. `flock -n` on a per-slot file is a counting semaphore with no shared
# counter to corrupt.
#
# The previous shape probed each slot with `flock -n "$slot" true` (acquire and
# release), then exec'd a BLOCKING `flock --timeout` on the slot it had seen
# free -- and if every slot was busy at probe time, blocked on slot 1
# specifically "so a queue forms in one place". Measured 2026-09-05 on s4 with
# five slots all held: every new job queued on slot 1 and stayed there while
# slots 4 and 5 came free, so the wrapper degraded to one job at a time exactly
# when the host was busiest. The probe-then-block race had the same effect at
# smaller scale (two jobs see slot 3 free, one loses and waits on slot 3 while
# slot 4 is idle).
#
# So the lock is taken for real, once, on an fd we open ourselves, and the job
# is exec'd holding that fd -- the lock lives as long as the job does, which is
# what `flock <file> <cmd>` gave us before. We use `exec {fd}>file` plus
# `flock -n $fd` (the fd form WITHOUT a command), never `flock "$fd" cmd`: that
# command form parses the fd number as a FILENAME, creates `./9`, and locks
# that -- three jobs at one slot hung 60 s that way (see git log for this line).
slot_deadline=$(( SECONDS + WAIT ))
while :; do
  for i in $(seq 1 "$SLOTS"); do
    slot="$LOCK.$i"
    touch "$slot" 2>/dev/null || slot="${TMPDIR:-/tmp}/axeyum-cargo.lock.$i"
    exec {slot_fd}>"$slot" || continue
    if flock -n "$slot_fd"; then
      exec "${run[@]}"
    fi
    exec {slot_fd}>&-
  done
  if [ "$SECONDS" -ge "$slot_deadline" ]; then
    echo "cargo-serialized: no slot free within ${WAIT}s (slots=$SLOTS lock=$LOCK)" >&2
    exit 75
  fi
  sleep 1
done
