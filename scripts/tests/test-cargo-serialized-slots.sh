#!/usr/bin/env bash
# Controls for the slot semaphore in scripts/cargo-serialized.sh.
#
# WHAT THIS EXISTS TO STOP. Measured 2026-09-05 on s4 with all five slots held:
# every new job queued on slot 1 and stayed there while slots 4 and 5 came
# free, because the wrapper probed the slots once, then blocked on slot 1 when
# all were busy. The wrapper degraded to one job at a time exactly when the
# host was busiest. Control 1 below is that scenario at two slots and dies on
# the previous code (exit 75 after the full WAIT instead of exit 0 in seconds).
#
# Every control uses a PRIVATE lock prefix under a temp dir, two slots, a
# trivial job (`sh -c`), no nice, no CPU weight -- so it never touches the
# host's real slots and runs in well under a minute.
#
# Usage: scripts/tests/test-cargo-serialized-slots.sh [path/to/cargo-serialized.sh]
#   The optional argument lets a mutation run point this suite at a copy.
set -uo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
wrapper="${1:-$here/../cargo-serialized.sh}"
[ -x "$wrapper" ] || { echo "not executable: $wrapper" >&2; exit 2; }

tmp=$(mktemp -d "${TMPDIR:-/var/tmp}/axeyum-cargo-slots-test.XXXXXX")
holders=()
cleanup() {
  for p in "${holders[@]:-}"; do [ -n "$p" ] && kill "$p" 2>/dev/null; done
  wait 2>/dev/null
  rm -rf "$tmp"
}
trap cleanup EXIT

export AXEYUM_CARGO_LOCK="$tmp/lock"
export AXEYUM_CARGO_SLOTS=2
export AXEYUM_CARGO_BIN=sh
export AXEYUM_CARGO_NICE=0
export AXEYUM_CARGO_CPUWEIGHT=0
touch "$AXEYUM_CARGO_LOCK" "$AXEYUM_CARGO_LOCK.1" "$AXEYUM_CARGO_LOCK.2"

failures=0
pass() { echo "PASS  $1"; }
fail() { echo "FAIL  $1" >&2; failures=$((failures + 1)); }

hold() { # hold <slot> <seconds>  -- background holder, registered for cleanup
  # The holder must BE the process that owns the lock fd, so that killing $!
  # releases the slot. `flock file sleep N &` would not do: killing the flock
  # parent orphans its `sleep` child, which inherited the fd and keeps the slot
  # held -- the first run of this suite found that out (controls 2 and 3 saw
  # both slots still held after cleanup).
  ( exec {hfd}>"$AXEYUM_CARGO_LOCK.$1" && flock "$hfd" && exec sleep "$2" ) &
  holders+=("$!")
}
wait_until_held() { # wait_until_held <slot>
  local n=0
  until ! flock -n "$AXEYUM_CARGO_LOCK.$1" true 2>/dev/null; do
    sleep 0.1; n=$((n + 1)); [ "$n" -gt 50 ] && return 1
  done
  return 0  # an `until` loop's status is its body's last command -- the [ ] above
}

# Control 1 -- THE INCIDENT. Both slots busy when the job arrives; slot 1 stays
# busy for the whole test, slot 2 frees after 3 s. The job must take slot 2 and
# finish in seconds. The previous code blocked on slot 1 and returned 75 after
# WAIT.
hold 1 60; hold 2 3
wait_until_held 1 && wait_until_held 2 || fail "control 1: holders did not take their slots"
start=$SECONDS
AXEYUM_CARGO_WAIT=20 "$wrapper" -c 'exit 0'
status=$?
elapsed=$(( SECONDS - start ))
if [ "$status" -eq 0 ] && [ "$elapsed" -lt 15 ]; then
  pass "control 1: job took the slot that freed (status=$status, ${elapsed}s)"
else
  fail "control 1: expected status 0 within 15 s, got status=$status after ${elapsed}s"
fi

# Control 2 -- fail-fast still works. Both slots held past WAIT: exit 75, the
# EX_TEMPFAIL the callers distinguish from a test failure.
hold 2 60
wait_until_held 2 || fail "control 2: holder did not take slot 2"
AXEYUM_CARGO_WAIT=2 "$wrapper" -c 'exit 0'
status=$?
if [ "$status" -eq 75 ]; then
  pass "control 2: no slot within WAIT exits 75"
else
  fail "control 2: expected 75, got $status"
fi

# Control 3 -- the job's own exit status is preserved once a slot is free, and
# a held slot does not leak: release everything, run a job that exits 7.
cleanup_holders() { for p in "${holders[@]}"; do kill "$p" 2>/dev/null; done; wait 2>/dev/null; holders=(); }
cleanup_holders
AXEYUM_CARGO_WAIT=5 "$wrapper" -c 'exit 7'
status=$?
if [ "$status" -eq 7 ]; then
  pass "control 3: job exit status preserved (7)"
else
  fail "control 3: expected 7, got $status"
fi

# Control 4 -- the lock is really held for the job's lifetime: a job that sleeps
# holds its slot, so a probe on that slot fails while it runs. With one slot
# only, a second job must wait for it (and must not run concurrently).
export AXEYUM_CARGO_SLOTS=1
AXEYUM_CARGO_WAIT=10 "$wrapper" -c 'sleep 3' &
job=$!
sleep 0.7
if flock -n "$AXEYUM_CARGO_LOCK.1" true 2>/dev/null; then
  fail "control 4: slot 1 was free while a job ran in it"
else
  pass "control 4: a running job holds its slot"
fi
wait "$job"

echo "CARGO_SERIALIZED_SLOTS|controls=4|failures=$failures"
[ "$failures" -eq 0 ]
