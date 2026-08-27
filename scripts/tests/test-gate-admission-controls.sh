#!/usr/bin/env bash
# Controls for the gate-admission mechanism landed 2026-08-27.
#
# Diagnosis: docs/research/11-design-review/2026-08-27-gate-throughput.md.
# The push battery starved because `scripts/cargo-serialized.sh` bounds MEMORY
# and nothing bounded CPU, and because the three things that consume this box
# called the wrapper zero times between them.
#
# Every assertion here is DISCRIMINATING -- it is paired with the input that
# makes it fail. The failure this repository keeps hitting is a check that
# cannot fail, and a scheduling change is an easy place to write one, because
# "it went faster" is not an exit status.
#
# Mutation-verified: each guard below was deleted in a scratch copy and exactly
# one case died. The mapping is recorded per case.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

W="$(mktemp -d "${TMPDIR:-/tmp}/axeyum-admission-XXXXXX")"
trap 'rm -rf "$W"' EXIT
CS=scripts/cargo-serialized.sh

fail=0
ok()   { echo "  ok   — $1"; }
bad()  { echo "  FAIL — $1"; fail=1; }
check(){ if [ "$2" = "$3" ]; then ok "$1"; else bad "$1 (want '$3', got '$2')"; fi; }

echo "=== gate admission controls ==="

# ---------------------------------------------------------------------------
# 1. `--slots` reports the host's admitted concurrency.
#
# It exists because CLAUDE.md, this lane's own brief, and three docs all said
# "one cargo at a time" nine days after the wrapper became a 5-slot semaphore.
# A number a tool prints cannot rot the way a sentence can.
# Guard: the `--slots` branch in cargo-serialized.sh.
# ---------------------------------------------------------------------------
slots="$("$CS" --slots 2>/dev/null)"
case "$slots" in
  ''|*[!0-9]*) bad "--slots prints an integer (got '$slots')" ;;
  *) if [ "$slots" -ge 1 ] && [ "$slots" -le 6 ]; then
       ok "--slots prints the admitted concurrency ($slots)"
     else
       bad "--slots out of the documented 1..6 clamp (got $slots)"
     fi ;;
esac

# ---------------------------------------------------------------------------
# 2. Lane work is niced, and the nice level is controllable.
#
# BOTH directions, because a control that only checks the default cannot tell
# "nice is applied" from "nice is the shell's ambient value". `AXEYUM_CARGO_NICE=0`
# is what `hooks/pre-push` sets, so the 0 case is the battery's own path.
# Guard: the `nice`/`ionice` block in cargo-serialized.sh.
# ---------------------------------------------------------------------------
if command -v nice >/dev/null 2>&1; then
  d="$("$CS" --batch nice 2>/dev/null | tr -d '[:space:]')"
  z="$(AXEYUM_CARGO_NICE=0 "$CS" --batch nice 2>/dev/null | tr -d '[:space:]')"
  check "default lane priority is nice 10" "$d" "10"
  check "AXEYUM_CARGO_NICE=0 disables it (the battery's path)" "$z" "0"
  if [ "$d" = "$z" ]; then
    bad "nice level is not actually controllable (both '$d')"
  fi
else
  echo "  skip — no nice(1) on this host"
fi

# ---------------------------------------------------------------------------
# 3. RE-ENTRANCY, tested against the deadlock it prevents.
#
# This is the case that matters. `scripts/check.sh` now takes a slot for its
# whole run, and steps inside it call the wrapper again. Without the marker the
# nested call takes a SECOND slot, and once every slot is held a wrapped script
# calling a wrapped script blocks for AXEYUM_CARGO_WAIT (default 5,400 s) --
# silently, looking exactly like a slow gate.
#
# So: hold EVERY slot, then run a job both ways with a 1-second wait.
#   marker set   -> must complete (no slot taken)
#   marker unset -> must report 75, the wrapper's "could not get a slot" status
# The second half is what makes the first half evidence: without it, the test
# would pass even if slots were never contended at all.
# Guard: the `AXEYUM_CARGO_SLOT_HELD` early `exec` in cargo-serialized.sh.
# ---------------------------------------------------------------------------
LK="$W/lock"
touch "$LK"
holders=()
for i in $(seq 1 "$slots"); do
  touch "$LK.$i"
  flock "$LK.$i" sleep 25 &
  holders+=("$!")
done
# Give the holders a moment to actually take their locks.
for _ in 1 2 3 4 5 6 7 8 9 10; do
  if ! flock -n "$LK.1" true 2>/dev/null; then break; fi
done

held_out="$(AXEYUM_CARGO_LOCK="$LK" AXEYUM_CARGO_WAIT=1 AXEYUM_CARGO_SLOT_HELD=1 \
            AXEYUM_CARGO_BIN=/bin/echo "$CS" REENTRANT 2>/dev/null)"
check "a job already inside a slot does not take a second one" "$held_out" "REENTRANT"

AXEYUM_CARGO_LOCK="$LK" AXEYUM_CARGO_WAIT=1 AXEYUM_CARGO_BIN=/bin/echo \
  "$CS" BLOCKED >/dev/null 2>&1
blocked_status=$?
check "positive control: without the marker every slot is genuinely busy (75)" \
  "$blocked_status" "75"

for h in "${holders[@]}"; do kill "$h" 2>/dev/null; done
wait 2>/dev/null

# ---------------------------------------------------------------------------
# 4. `--batch` runs a non-cargo command and exports the marker to it.
#
# `scripts/check.sh` re-execs itself through this. If the marker did not reach
# the child, every nested step would queue for its own slot behind a gate that
# already holds one -- case 3's deadlock, arrived at from the other side.
# Guard: the `--batch` branch and the `export AXEYUM_CARGO_SLOT_HELD=1`.
# ---------------------------------------------------------------------------
b="$("$CS" --batch /bin/sh -c 'echo "$AXEYUM_CARGO_SLOT_HELD"' 2>/dev/null)"
check "--batch exports the re-entrancy marker to its child" "$b" "1"

# ---------------------------------------------------------------------------
# 5. The memory ceiling STILL BITES for an ordinary job.
#
# The whole point of the wrapper is that a runaway job dies instead of the host
# (or the agent). A scheduling change that quietly defeated the cgroup would be
# the worst possible outcome, so this re-runs the wrapper's own probe. Skipped
# where the user systemd manager cannot delegate memory, because there the
# probe's failure is a host fact and not a regression.
# Guard: the systemd-run scope construction in cargo-serialized.sh.
# ---------------------------------------------------------------------------
if systemctl --user show-environment >/dev/null 2>&1; then
  if "$CS" --self-check >/dev/null 2>&1; then
    ok "MemoryMax still enforced after the priority change (--self-check)"
  else
    bad "--self-check no longer reports enforced; the ceiling is decoration"
  fi
else
  echo "  skip — no user systemd manager; ceiling not assertable here"
fi

# ---------------------------------------------------------------------------
# 6. `--batch` applies NO memory scope.
#
# Deliberate: a batch is a supervisor. `MemoryMax=24G` on `scripts/check.sh`
# would have the cgroup SIGKILL the aggregate gate at a threshold no individual
# step exceeded, and the gate would report a failure that is not a failure.
# Asserted rather than commented, because the difference is invisible from the
# outside until the day it kills a green run.
# Guard: the `if [ "$BATCH" = "1" ]; then :` arm around the scope.
# ---------------------------------------------------------------------------
if systemctl --user show-environment >/dev/null 2>&1; then
  probe='b = bytearray(400 * 1024 * 1024); print("SURVIVED")'
  bo="$(AXEYUM_CARGO_MEM=64M "$CS" --batch python3 -c "$probe" 2>/dev/null)"
  check "--batch is not memory-scoped (a supervisor is not a cargo job)" \
    "$bo" "SURVIVED"
else
  echo "  skip — no user systemd manager"
fi

# ---------------------------------------------------------------------------
# 6b. CPU WEIGHT, and — the part that matters — AT THE RIGHT CGROUP LEVEL.
#
# `nice` alone measured as doing NOTHING (1.85x vs 1.82x, 27 competitors in both
# arms) because `sched_autogroup_enabled=1` keeps nice inside a session. The
# cgroup `cpu` controller is what crosses the boundary, and two attempts at it
# were correctly APPLIED and completely INEFFECTIVE:
#
#   scope only          user@.service/app.slice/run-*.scope        weight 10
#   --slice=axeyum-lane user@.service/axeyum.slice/axeyum-lane...  weight 10
#
# In both, the sibling of the session scope holding the battery was some OTHER
# cgroup at the default weight, so the 10 ordered lane jobs against each other
# and nothing else. Reading `cpu.weight` back said "applied" both times.
#
# So this asserts the LEVEL, not just the value: the job's cgroup must sit
# directly under the same parent as an ordinary session scope. A test that only
# checked `cpu.weight = 10` would have passed on both broken versions.
# Guard: the `--slice=axeyumlane` + `set-property` block in cargo-serialized.sh.
# ---------------------------------------------------------------------------
if systemctl --user show-environment >/dev/null 2>&1 \
   && [ -r /proc/self/cgroup ]; then
  cg_prog='import sys; print(open("/proc/self/cgroup").read().strip().split("::")[1])'
  mine="$(python3 -c "$cg_prog" 2>/dev/null)"
  jobcg="$(AXEYUM_CARGO_BIN=python3 "$CS" -c "$cg_prog" 2>/dev/null | tail -1)"
  off="$(AXEYUM_CARGO_CPUWEIGHT=0 AXEYUM_CARGO_BIN=python3 "$CS" -c "$cg_prog" 2>/dev/null | tail -1)"
  case "$jobcg" in
    */axeyumlane.slice/*) ok "lane work runs in axeyumlane.slice" ;;
    *) bad "lane work is not in axeyumlane.slice (got '$jobcg')" ;;
  esac
  # The level assertion: strip the leaf scope from each and compare parents.
  mine_parent="${mine%/*}"
  job_parent="${jobcg%/*}"        # .../axeyumlane.slice
  job_gparent="${job_parent%/*}"  # .../user@N.service
  if [ "$job_gparent" = "$mine_parent" ]; then
    ok "…and that slice is a SIBLING of an ordinary session scope"
  else
    bad "slice is at the wrong cgroup level: session parent '$mine_parent' vs slice parent '$job_gparent' — the weight will order lane jobs against each other and nothing else"
  fi
  case "$off" in
    */axeyumlane.slice/*) bad "AXEYUM_CARGO_CPUWEIGHT=0 still used the lane slice" ;;
    '') echo "  skip — could not read the opted-out job's cgroup" ;;
    *) ok "control: AXEYUM_CARGO_CPUWEIGHT=0 opts out of the slice" ;;
  esac
else
  echo "  skip — no user systemd manager / cgroup v2 readable here"
fi

# ---------------------------------------------------------------------------
# 7. `hooks/pre-push` sees a Cargo.lock-only change.
#
# It did not until 2026-08-27: `'*.rs' '*.toml'` does not match `Cargo.lock`, so
# a dependency bump skipped the entire battery. Tested on the real pathspec
# rather than by reading the hook, and paired with the negative that documents
# WHY it was missed.
# Guard: the `'Cargo.lock'` pathspec entry in hooks/pre-push.
# ---------------------------------------------------------------------------
if grep -c "'Cargo.lock'" hooks/pre-push >/dev/null 2>&1 \
   && [ "$(grep -c "'Cargo.lock'" hooks/pre-push)" -ge 1 ]; then
  ok "pre-push change filter names Cargo.lock"
else
  bad "pre-push change filter omits Cargo.lock (a dep bump skips the battery)"
fi
# The control that explains WHY it was missed, using the same glob semantics
# git's pathspec applies to a basename. Deliberately not `git ls-files`: this
# suite must be runnable against a scratch copy of four files (that is how
# `mutate-gate-admission.sh` avoids mutating a checkout other lanes compile
# from), and a git query would bind it to a real repository.
case "Cargo.lock" in
  *.toml) bad "'*.toml' matches Cargo.lock, so this whole case is moot — re-derive it" ;;
  *)      ok  "control: '*.toml' genuinely does not match Cargo.lock" ;;
esac

# ---------------------------------------------------------------------------
# 8. `scripts/check.sh` takes a slot, and its STEP LIST is unchanged by that.
#
# The step list is what `scripts/check-aggregate-scope.sh` compares against the
# justfile. A scheduling wrapper that silently dropped a step would be exactly
# the "fast because vacuous" failure this change must not commit.
# Guard: the `--batch` re-exec block at the top of check.sh.
# ---------------------------------------------------------------------------
if [ "$(grep -c 'cargo-serialized.sh --batch' scripts/check.sh)" -ge 1 ]; then
  ok "check.sh routes itself through the semaphore"
else
  bad "check.sh takes no cargo slot; the semaphore is unwired again"
fi
n_steps="$(AXEYUM_CHECK_LIST=1 ./scripts/check.sh 2>/dev/null | grep -c .)"
if [ "$n_steps" -gt 50 ]; then
  ok "check.sh still enumerates its steps under the wrapper ($n_steps)"
else
  bad "check.sh enumerated $n_steps steps — the listing path is broken"
fi

echo
if [ "$fail" = "0" ]; then
  echo "gate admission controls: ok"
else
  echo "gate admission controls: FAILED"
fi
exit "$fail"
