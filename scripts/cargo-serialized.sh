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
# Usage:
#   scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full
#   scripts/cargo-serialized.sh --self-check   # does the ceiling actually bite HERE?
#   AXEYUM_CARGO_MEM=48G scripts/cargo-serialized.sh test --workspace --all-features
#
# Env:
#   AXEYUM_CARGO_SLOTS concurrent jobs on this host (default: RAM / MEM, 1..6)
#   AXEYUM_CARGO_MEM   scope MemoryMax          (default 24G)
#   AXEYUM_CARGO_SWAP  scope MemorySwapMax      (default 0 -- see above)
#   AXEYUM_CARGO_WAIT  seconds to wait for lock (default 5400; 0 = fail fast)
#   AXEYUM_CARGO_CPUS  taskset list             (default unset -- no pinning)
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

if [ "$#" -eq 0 ]; then
  echo "usage: $0 <cargo args...>   |   $0 --self-check" >&2
  exit 2
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
run=("${AXEYUM_CARGO_BIN:-cargo}" "$@")
if [ -n "${AXEYUM_CARGO_CPUS:-}" ]; then
  run=(taskset -c "$AXEYUM_CARGO_CPUS" "${run[@]}")
fi
# `--scope` runs it as a child of THIS shell's cgroup rather than a transient
# service, so stdout/stderr and the exit status pass through unchanged. Without
# a working user manager (a bare ssh session may have none) fall back to running
# it directly: the lock is still worth having even when the ceiling is not.
if systemctl --user show-environment >/dev/null 2>&1; then
  run=(systemd-run --user --scope -q \
       -p "MemoryMax=$MEM" -p "MemorySwapMax=$SWAP" "${run[@]}")
else
  echo "cargo-serialized: no user systemd manager; running WITHOUT MemoryMax=$MEM" >&2
fi

# Take the first FREE slot without blocking; only if every slot is busy do we
# wait, and then on slot 1 -- so a queue forms in one place instead of N lanes
# each polling. `flock -n` on a per-slot file is a counting semaphore with no
# shared counter to corrupt.
# NOT the file-descriptor form. `flock <fd>` takes no command, so
# `flock "$fd" cmd` is parsed as `flock <FILE> <cmd>` with the fd NUMBER as the
# filename -- it silently creates `./9` in the current directory, locks that, and
# three jobs at one slot hung for 60 s under a `timeout` instead of taking 9 s.
# The file form with a probe is simpler and cannot do that. The probe races (two
# jobs can both see a slot free), and losing that race is correct behaviour, not
# a bug: the loser blocks on the same slot with the same timeout it would have
# waited anyway.
for i in $(seq 1 "$SLOTS"); do
  slot="$LOCK.$i"
  touch "$slot" 2>/dev/null || slot="${TMPDIR:-/tmp}/axeyum-cargo.lock.$i"
  if flock -n "$slot" true 2>/dev/null; then
    exec flock --timeout "$WAIT" --conflict-exit-code 75 "$slot" "${run[@]}"
  fi
done
exec flock --timeout "$WAIT" --conflict-exit-code 75 "$LOCK.1" "${run[@]}"
