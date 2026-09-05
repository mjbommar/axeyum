#!/usr/bin/env bash
# The `by axeyum` gate: build `lean/axeyum-tactic` with the PINNED toolchain,
# run its test library, and enforce floors on what the run actually did.
#
# Why the counting, rather than just the exit status. `lake build` exiting 0
# cannot distinguish "closed eleven Lean goals through Axeyum" from "found
# nothing to do because everything was cached" from "the test library has no
# roots" -- and this repository has shipped all three shapes of green-looking
# gate (see `scripts/check-gate-liveness.sh` and the `--features full` traps in
# CLAUDE.md). So this script:
#
#   1. RESOLVES the pinned Lean by delegating to `scripts/check-lean-gate.sh
#      --print-toolchain`, which is the single implementation of that policy,
#      and PRINTS which binary it got (`AXEYUM-LEAN-TOOLCHAIN`).
#   2. DELETES the Tests build products first, so the counts below come from
#      this run and not from a cache. Lake is correct about staleness but
#      silent about it: a cached module prints none of its `logInfo` lines, and
#      a gate that read zero and passed would be exactly the defect.
#   3. COUNTS three things the run must have done, each with a floor:
#        - goals ACCEPTED   (`Tests/NatLinear.lean`, from Lean's environment)
#        - shim rows        (`Tests/ShimCorrespondence.lean`, likewise)
#        - mutations REJECTED (`Tests/Mutations.lean`) -- counted by reading
#          the file, because Lean cannot count its own `#guard_msgs` blocks;
#          that the file ELABORATED is what says each one matched.
#   4. Requires the mutation file's positive control to have closed, so a
#      tactic that always failed could not pass the battery.
#
# Every floor is a ratchet: raising one as the fragment grows is the gate
# working; lowering one needs a reason in the commit message.
#
# Usage:
#   scripts/check-lean-tactic.sh
#   AXEYUM_ALLOW_NO_LEAN=1 scripts/check-lean-tactic.sh   # loud SKIP, exit 0
#   AXEYUM_LEAN_ALLOW_UNPINNED=1 …                        # stated deviation
#
# ADR-1666.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

PACKAGE_DIR="lean/axeyum-tactic"
SIDECAR="target/release/examples/axeyum_sidecar"

# Floors, measured 2026-09-05 on leanprover/lean4:v4.34.0-rc1 (commit
# 3447a668783dbce1a8fdb97101dd067687b2b418): 11 goals accepted, 13 shim rows,
# 11 mutations rejected, 1 positive control.
GOAL_FLOOR=11
SHIM_ROW_FLOOR=13
MUTATION_FLOOR=11
CONTROL_FLOOR=1

# ---------------------------------------------------------------------------
# 1. The toolchain. One policy, implemented once, in check-lean-gate.sh.
# ---------------------------------------------------------------------------
toolchain_report=$(scripts/check-lean-gate.sh --print-toolchain 2>&1)
toolchain_status=$?
if [ "$toolchain_status" -ne 0 ]; then
  if [ "${AXEYUM_ALLOW_NO_LEAN:-}" = "1" ]; then
    echo "check-lean-tactic: SKIPPED -- 0 Lean goals were checked. This is NOT a pass;" \
         "AXEYUM_ALLOW_NO_LEAN=1 was set, so no real Lean saw a term Axeyum produced." >&2
    exit 0
  fi
  echo "check-lean-tactic: FAILED -- could not resolve the pinned Lean:" >&2
  printf '%s\n' "$toolchain_report" >&2
  exit 1
fi

lean_bin=$(printf '%s\n' "$toolchain_report" | sed -n 's/^bin=//p')
lean_version=$(printf '%s\n' "$toolchain_report" | sed -n 's/^version=//p')
lean_pin=$(printf '%s\n' "$toolchain_report" | sed -n 's/^pin=//p')
if [ -z "$lean_bin" ] || [ ! -x "$lean_bin" ]; then
  # check-lean-gate.sh's OWN skip path exits 0 under AXEYUM_ALLOW_NO_LEAN=1
  # while printing no `bin=` line, so the branch above (which keys on its exit
  # status) never sees it and this one has to. Found by running the skip path
  # as a control rather than assuming it: without this, a host with no pinned
  # Lean and the flag set FAILED with "printed no usable bin= line" instead of
  # skipping. Wrong in the safe direction, but still wrong.
  if [ "${AXEYUM_ALLOW_NO_LEAN:-}" = "1" ]; then
    echo "check-lean-tactic: SKIPPED -- 0 Lean goals were checked. This is NOT a pass;" \
         "AXEYUM_ALLOW_NO_LEAN=1 was set, so no real Lean saw a term Axeyum produced." >&2
    exit 0
  fi
  echo "check-lean-tactic: FAILED -- check-lean-gate.sh printed no usable bin= line." >&2
  printf '%s\n' "$toolchain_report" >&2
  exit 1
fi

lake_bin="$(dirname "$lean_bin")/lake"
if [ ! -x "$lake_bin" ]; then
  echo "check-lean-tactic: FAILED -- no \`lake\` beside the resolved Lean ($lake_bin)." \
       "A toolchain without lake cannot build the package." >&2
  exit 1
fi

echo "AXEYUM-LEAN-TOOLCHAIN lean-tactic bin=$lean_bin version=$lean_version"
echo "check-lean-tactic: pin $lean_pin; lake $lake_bin"

package_pin=$(tr -d '[:space:]' <"$PACKAGE_DIR/lean-toolchain" 2>/dev/null)
if [ "$package_pin" != "$lean_pin" ]; then
  echo "check-lean-tactic: FAILED -- $PACKAGE_DIR/lean-toolchain says '$package_pin'" \
       "but the repository pin is '$lean_pin'. The package must follow the repository's" \
       "single pin, or a green run here says nothing about the Lean everything else uses." >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# 2. The sidecar. Built here rather than assumed, so a stale binary cannot
#    silently answer for a source tree it does not match.
# ---------------------------------------------------------------------------
if [ -x scripts/cargo-serialized.sh ]; then
  cargo_runner="scripts/cargo-serialized.sh"
else
  cargo_runner="cargo"
fi
echo "check-lean-tactic: building the sidecar ($cargo_runner)"
if ! "$cargo_runner" build --release -p axeyum-lean-import --example axeyum_sidecar; then
  echo "check-lean-tactic: FAILED -- the sidecar did not build." >&2
  exit 1
fi
if [ ! -x "$SIDECAR" ]; then
  echo "check-lean-tactic: FAILED -- $SIDECAR is missing after a successful build." >&2
  exit 1
fi
sidecar_abs="$PWD/$SIDECAR"

# ---------------------------------------------------------------------------
# 3. The run. Tests build products are removed first so the counts are this
#    run's, and the tactic's own relative stub paths resolve from the package
#    directory.
# ---------------------------------------------------------------------------
rm -rf "$PACKAGE_DIR/.lake/build/lib/lean/Tests" "$PACKAGE_DIR/.lake/build/ir/Tests"

log=$(mktemp) || exit 2
trap 'rm -f "$log"' EXIT

(
  cd "$PACKAGE_DIR" || exit 2
  AXEYUM_SIDECAR="$sidecar_abs" "$lake_bin" build
) >"$log" 2>&1
build_status=$?

sed 's/^/check-lean-tactic| /' "$log"

if [ "$build_status" -ne 0 ]; then
  echo "check-lean-tactic: FAILED -- \`lake build\` exited $build_status." \
       "Every test in this package is a goal Lean either elaborates or does not," \
       "so a nonzero exit is a goal that stopped closing or a mutation that stopped" \
       "being rejected." >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# 4. The counts.
# ---------------------------------------------------------------------------
goals=$(sed -n 's/.*AXEYUM-TACTIC-ACCEPTED goals=\([0-9][0-9]*\).*/\1/p' "$log" | tail -1)
shim_rows=$(sed -n 's/.*AXEYUM-TACTIC-SHIM-ROWS rows=\([0-9][0-9]*\).*/\1/p' "$log" | tail -1)
controls=$(sed -n 's/.*AXEYUM-TACTIC-MUTATIONS controls=\([0-9][0-9]*\).*/\1/p' "$log" | tail -1)
mutations=$(grep -c '#guard_msgs in' "$PACKAGE_DIR/Tests/Mutations.lean")

goals=${goals:-0}
shim_rows=${shim_rows:-0}
controls=${controls:-0}
mutations=${mutations:-0}

echo "check-lean-tactic: goals-accepted=$goals mutations-rejected=$mutations" \
     "shim-rows=$shim_rows controls=$controls"

fail=0
if [ "$goals" -lt "$GOAL_FLOOR" ]; then
  echo "check-lean-tactic: FAILED -- $goals goal(s) accepted, floor is $GOAL_FLOOR." \
       "A run that accepts zero goals exits 0 from lake exactly like one that accepts" \
       "eleven; that is why this is counted." >&2
  fail=1
fi
if [ "$mutations" -lt "$MUTATION_FLOOR" ]; then
  echo "check-lean-tactic: FAILED -- $mutations mutation(s) in Tests/Mutations.lean," \
       "floor is $MUTATION_FLOOR. The count is read from the file because Lean cannot" \
       "count its own \`#guard_msgs\` blocks; that the file elaborated is what says each" \
       "one still matched its pinned message." >&2
  fail=1
fi
if [ "$shim_rows" -lt "$SHIM_ROW_FLOOR" ]; then
  echo "check-lean-tactic: FAILED -- $shim_rows shim row(s), floor is $SHIM_ROW_FLOOR." \
       "A row that vanished takes a name-map entry's target with it, and the bridge would" \
       "then print a constant Lean does not have." >&2
  fail=1
fi
if [ "$controls" -lt "$CONTROL_FLOOR" ]; then
  echo "check-lean-tactic: FAILED -- $controls positive control(s) in the mutation" \
       "battery, floor is $CONTROL_FLOOR. Without one, a tactic that ALWAYS failed would" \
       "pass every mutation." >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  exit 1
fi

echo "check-lean-tactic: OK -- $goals Lean goal(s) closed by a term Axeyum produced and" \
     "Lean's kernel checked; $mutations mutation(s) rejected; $shim_rows shim row(s) proved" \
     "from Lean core; checker $lean_bin ($lean_version)."
exit 0
