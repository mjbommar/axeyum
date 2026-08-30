#!/usr/bin/env bash
# Tier-0 of the aggregate gate: run EVERY step `scripts/check.sh` declares, each
# under a hard per-step time cap, and report three outcomes -- ok / FAILED /
# DEFERRED -- never two.
#
# # Why this exists
#
# Measured 2026-08-29 in a lane worktree. `scripts/check.sh` declares **379**
# steps. Sampling every 5th non-cargo step (71 of 355) took **549 s**, and
# **15 of those 71 steps accounted for 528 s of it** -- the other 56 averaged
# ~0.4 s. Extrapolated, the aggregate gate is well over an hour, and the fast
# ~80% of its steps cost ~4% of its time.
#
# That cost is not a nuisance; it is the mechanism of gate rot. Neither
# `hooks/pre-push` nor `.github/workflows/ci.yml` invokes `scripts/check.sh` or
# `just check` -- verified by name, with a positive control (both DO name
# `scripts/check-kernel-suites.sh`). The aggregate gate's only caller is a human
# typing it, so `scripts/check-local-ci-freshness.sh` -- the gate whose entire
# job is to notice the battery has gone stale -- sat RED for **265 h / 3,974
# commits**, because its only caller was the gate that had gone stale. A
# staleness detector reachable only from the thing it detects staleness in
# cannot fire.
#
# This script makes the cheap 80% runnable in ~2 minutes so that a lane, a hook,
# or a coordinator between merges can run *something* unconditionally.
#
# # The one thing this must never do
#
# **A deferred step must never read as a passing step.** That is the
# checker-that-cannot-fail defect wearing a performance optimization's clothes,
# and this repository has shipped it five times. So:
#
#   * the summary line always carries `NOT-A-FULL-GATE`, on every exit path;
#   * DEFERRED is a third outcome with its own counter, never folded into `ok`;
#   * an empty step list is a FAILURE (exit 2), not a clean run of nothing.
#
# Exit status: 0 = every step that RAN passed; 1 = at least one step FAILED;
# 2 = the gate could not enumerate any steps (vacuous run).
#
# Usage:
#   scripts/check-fast.sh                 # 3 s cap, cargo steps deferred
#   scripts/check-fast.sh --budget 10     # 10 s cap
#   scripts/check-fast.sh --with-cargo    # also attempt cargo steps
#
# Testability hook: AXEYUM_CHECK_FAST_LIST_CMD overrides the enumeration
# command, so `scripts/tests/test-check-fast.sh` can feed a fixture step list
# without running the real gate.
set -uo pipefail

cd "$(dirname "$0")/.."

budget=3
with_cargo=0
while [ $# -gt 0 ]; do
  case "$1" in
    --budget) budget="${2:?--budget needs a value}"; shift 2 ;;
    --with-cargo) with_cargo=1; shift ;;
    -h|--help) sed -n '1,45p' "$0"; exit 0 ;;
    *) echo "check-fast: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

list_cmd="${AXEYUM_CHECK_FAST_LIST_CMD:-}"
if [ -z "$list_cmd" ]; then
  list_cmd="env AXEYUM_CHECK_LIST=1 AXEYUM_CHECK_NO_SLOT=1 scripts/check.sh"
fi

steps_file="$(mktemp)"
trap 'rm -f "$steps_file"' EXIT
if ! $list_cmd > "$steps_file" 2>/dev/null; then
  echo "check-fast: could not enumerate steps via: $list_cmd" >&2
fi

# VACUITY GUARD. A run over zero steps prints a perfect green summary and
# checks nothing -- the exact shape of every inert gate this repository has
# shipped. Exit 2, distinct from a step failure, so a caller can tell them
# apart.
n_declared=$(grep -c . "$steps_file" || true)
if [ "${n_declared:-0}" -lt 1 ]; then
  echo "CHECK_FAST|NOT-A-FULL-GATE|declared=0|VACUOUS: the step list is empty" >&2
  exit 2
fi

ok=0
failed=0
deferred=0
failed_names=()
deferred_names=()

while IFS=$'\t' read -r name cmd; do
  [ -n "${name:-}" ] || continue
  [ -n "${cmd:-}" ] || continue
  # Cargo steps take the host-wide serialization flock and will exhaust any
  # tier-0 budget by construction. Defer them by DECLARATION rather than by
  # burning the budget discovering it again; `--with-cargo` opts back in.
  #
  # A `case` glob and NOT `printf ... | grep -q`: CLAUDE.md's banned-idiom list
  # is explicit that `grep -q` consuming a pipeline under `set -o pipefail`
  # SIGPIPEs its producer, yielding status 141, which `pipefail` then reports as
  # "not found". Same tree, different answer on consecutive runs.
  # HOST-CONDITIONAL steps, marked `optional:` in field 1 by `scripts/check.sh`.
  # The full gate wraps these in a toolchain test (`command -v uv && [ -d .venv ]`)
  # and skips them when the toolchain is absent; this sweep enumerates through the
  # same list and would otherwise RUN them and count 8 host-setup failures as gate
  # failures.
  #
  # They are counted and NAMED, never silently dropped -- an absent gate that
  # prints nothing is indistinguishable from a gate that ran, which is the exact
  # defect this script's three-outcome contract exists to prevent. They land in
  # `deferred`, whose banner already says DEFERRED means UNCHECKED.
  case "$name" in
    optional:*)
      deferred=$((deferred + 1))
      deferred_names+=("${name#optional:}(host-conditional)")
      continue
      ;;
  esac
  if [ "$with_cargo" -eq 0 ]; then
    case "$cmd" in
      *cargo*)
        deferred=$((deferred + 1))
        deferred_names+=("$name(cargo)")
        continue
        ;;
    esac
  fi
  # `--kill-after` IS NOT OPTIONAL, and without it this line was decoration.
  #
  # `timeout N` sends SIGTERM at the deadline and then waits FOREVER for the
  # child to die. A step that ignores or is wedged inside a TERM handler is not
  # bounded at all -- and `timeout` still exits 124, so the caller sees a
  # correct-looking "timed out" verdict after an arbitrarily long wait. The
  # status is right and the bound is fiction. Measured on this host:
  #
  #   trap '' TERM; sleep 25
  #   timeout 2      ./that.sh  ->  exit 124 after 25s
  #   timeout -k 1 2 ./that.sh  ->  exit 137 after  3s
  #
  # This was live here: a run of THIS script was found stuck 23 minutes on a
  # step with a 3-second budget (`scripts/tests/mutate-gate-admission.sh`),
  # its child shell alive and its grandchildren `<defunct>` -- i.e. wedged
  # inside its own `trap ... EXIT` cleanup. The tool whose entire purpose is
  # per-step capping had a cap that could not fire.
  #
  # GRACE = 5s, and the number is a choice. It has to cover an ordinary EXIT
  # trap -- these scripts clean up scratch directories, which is sub-second
  # here -- and no more, because the real bound is `budget + grace` per step
  # and this is a tier-0 sweep where the budget is 3s. 30s (what the full gate
  # uses, where it is 1.7% of a 30-minute cap) would be 10x the budget here.
  # `setsid` and the GROUP kill below: `timeout` bounds the step but does not
  # kill its descendants -- an ignored SIGTERM disposition is inherited across
  # exec, so a grandchild outlives the cap and keeps whatever lock it took.
  # Measured with a positive control, four `timeout` spellings all left the
  # grandchild alive; `setsid` + `kill -KILL -$pgid` leaves none.
  # `scripts/check.sh` carries the same construction and the long version of
  # this comment.
  setsid timeout --kill-after="${AXEYUM_CHECK_FAST_KILL_GRACE:-5}" "$budget" \
    bash -c "$cmd" >/dev/null 2>&1 </dev/null &
  pid=$!
  pgid="$(ps -o pgid= -p "$pid" 2>/dev/null | tr -d ' ')"
  wait "$pid"
  st=$?
  if { [ "$st" -eq 124 ] || [ "$st" -eq 137 ]; } \
     && [ -n "$pgid" ] && [ "$pgid" = "$pid" ]; then
    kill -KILL -"$pgid" 2>/dev/null
  fi
  if [ "$st" -eq 0 ]; then
    ok=$((ok + 1))
  elif [ "$st" -eq 124 ] || [ "$st" -eq 137 ]; then
    # Over budget. NOT a failure and NOT a pass -- a third outcome.
    deferred=$((deferred + 1))
    deferred_names+=("$name(over-${budget}s)")
  else
    failed=$((failed + 1))
    failed_names+=("$name")
    echo "--- $name: FAILED (exit $st)  -- $cmd"
  fi
done < "$steps_file"

echo
echo "CHECK_FAST|NOT-A-FULL-GATE|declared=${n_declared}|ok=${ok}|failed=${failed}|deferred=${deferred}|budget=${budget}s"
if [ "$deferred" -gt 0 ]; then
  echo "  DEFERRED (neither passed nor failed -- these are UNCHECKED):"
  printf '    %s\n' "${deferred_names[@]}"
fi
if [ "$failed" -gt 0 ]; then
  echo "  FAILED:"
  printf '    %s\n' "${failed_names[@]}"
  exit 1
fi
exit 0
