#!/usr/bin/env bash
# Mutation controls for scripts/check-kernel-differential.py's six guards.
#
# CLAUDE.md's standing rule: when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies. This suite does that for real, against
# a MUTATED COPY of the shipped script (never the tracked file -- mutating a
# file on disk in a shared checkout breaks other lanes' builds, see CLAUDE.md
# "MUTATION TESTING IN THE SHARED WORKTREE BREAKS OTHER LANES' BUILDS").
#
# Each mutation disables exactly one of G1..G6 in `evaluate()` and re-runs
# `--self-test`. `--self-test` already asserts each fixture's EXPECTED guard
# fires (see check-kernel-differential.py's `self_test()`); disabling a guard
# must make its OWN fixture's assertion fail while every other fixture keeps
# passing. This is checked by parsing which fixture names report
# "SELF-TEST FAIL" -- exactly the one named for that guard, no more, no
# fewer.
set -u
cd "$(dirname "$0")/../.." || exit 2

SRC="scripts/check-kernel-differential.py"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

fail=0

# name -> (old snippet, new snippet, expected failing fixture)
run_case() {
  local label="$1" old="$2" new="$3" expect_fixture="$4"
  local mutant="$SCRATCH/mutant-$label.py"
  python3 - "$SRC" "$mutant" "$old" "$new" <<'PY'
import sys
src_path, out_path, old, new = sys.argv[1:5]
text = open(src_path).read()
if old not in text:
    print(f"MUTATION SETUP FAILED for old snippet not found: {old!r}")
    sys.exit(2)
if text.count(old) != 1:
    print(f"MUTATION SETUP FAILED: snippet is not unique ({text.count(old)} occurrences): {old!r}")
    sys.exit(2)
text = text.replace(old, new)
open(out_path, "w").write(text)
PY
  if [ $? -ne 0 ]; then
    echo "FAIL [$label]: could not construct mutant"
    fail=1
    return
  fi

  local out
  out="$(python3 "$mutant" --self-test 2>&1)"
  local rc=$?

  # Every fixture that reported SELF-TEST FAIL, by its bracketed label.
  local failing_fixtures
  failing_fixtures="$(printf '%s\n' "$out" | grep -oE '^SELF-TEST FAIL \[[a-z0-9-]+\]' | sed -E 's/^SELF-TEST FAIL \[([a-z0-9-]+)\]/\1/' | sort -u)"
  local n_failing
  n_failing="$(printf '%s\n' "$failing_fixtures" | grep -c . || true)"

  if [ "$rc" -eq 0 ]; then
    echo "FAIL [$label]: mutant self-test exited 0 -- deleting this guard killed NOTHING"
    fail=1
    return
  fi
  if [ "$n_failing" -ne 1 ]; then
    echo "FAIL [$label]: expected exactly 1 fixture to fail, got $n_failing: [$failing_fixtures]"
    fail=1
    return
  fi
  if [ "$failing_fixtures" != "$expect_fixture" ]; then
    echo "FAIL [$label]: expected fixture [$expect_fixture] to fail, got [$failing_fixtures]"
    fail=1
    return
  fi
  echo "ok [$label]: deleting this guard kills exactly [$expect_fixture], nothing else"
}

# G2: corpus non-empty.
run_case "G2" \
  'if not cases:' \
  'if False and not cases:' \
  "empty-corpus"

# G3: per-subsystem non-empty (the whole for-loop's condition).
run_case "G3" \
  'if counts.get(subsystem, 0) == 0:' \
  'if False and counts.get(subsystem, 0) == 0:' \
  "missing-subsystem"

# G4: Lean actually invoked.
run_case "G4" \
  'if checked is None:' \
  'if False and checked is None:' \
  "lean-not-invoked"

# G5: zero P0 disagreements.
run_case "G5" \
  '''p0 = [c for c in cases if c["verdict"] == "AxeyumAcceptsLeanRejects"]''' \
  '''p0 = []  # MUTATED: guard disabled''' \
  "p0-disagreement"

# G6: zero unexplained incompleteness.
run_case "G6" \
  'if case["name"] not in EXPLAINED_INCOMPLETENESS:' \
  'if False and case["name"] not in EXPLAINED_INCOMPLETENESS:' \
  "unexplained-incompleteness"

# G1: the process's own exit status.
run_case "G1" \
  'if returncode != 0:' \
  'if False and returncode != 0:' \
  "nonzero-exit"

if [ "$fail" -ne 0 ]; then
  echo "test-kernel-differential-gate: FAILED"
  exit 1
fi
echo "test-kernel-differential-gate: all six guards independently mutation-verified"
exit 0
