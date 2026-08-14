#!/usr/bin/env bash
# The workspace test sweep, reporting HOW MANY TESTS IT RAN and what it skipped.
#
# Two failure modes this wraps, both measured in this repository:
#
#   * "running 0 tests ... ok". A suite emptied by a new `#![cfg(feature = ...)]`
#     exits 0. `corpus_regression` sat inert that way for 15 days
#     (`scripts/check-gate-liveness.sh` has the full list). A gate that does not
#     print a count cannot be checked for this by the person reading its output.
#   * A test that PASSES over source it never compiled. Cargo's freshness is
#     mtime-based, so a source file older than the cached artifact is invisible
#     (measured 2026-08-14: rewrite `answer()` from 1 to 99, `touch -d 2020-01-01`
#     the file, and `cargo test` still prints "1 passed"). `git archive | tar -x`
#     — the snapshot build every lane is told to use — stamps files with the
#     commit time, which is exactly this. See `scripts/check-source-freshness.sh`.
#
# What it prints: total tests run, how many binaries they came from, how many
# were filtered out, and — the part that matters — WHICH suites are excluded
# here and where they run instead.
#
# Usage: scripts/check-workspace-tests.sh [extra cargo test args...]
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
root="$PWD"

"$root/scripts/check-source-freshness.sh" --gate test --touch || exit 2

log="$(mktemp)" || exit 2
trap 'rm -f "$log"' EXIT

# `frontier_*` is skipped deliberately: those ratchets are wall-clock budgets and
# contention from a parallel sweep shrinks the measured frontier into a false
# REGRESSION (measured 2026-07-30). They run serialized in their own step.
cargo test --workspace --all-features "$@" -- --skip frontier_ 2>&1 | tee "$log"
status=${PIPESTATUS[0]}

TEST_LOG="$log" python3 - <<'PY'
import os, re, sys

pattern = re.compile(
    r"test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored; "
    r"(\d+) measured; (\d+) filtered out"
)
passed = failed = ignored = filtered = 0
suites = 0
empty = []
current = None

with open(os.environ["TEST_LOG"], "r", errors="replace") as handle:
    for line in handle:
        if line.startswith("     Running ") or line.startswith("   Doc-tests "):
            current = line.strip()
        match = pattern.search(line)
        if not match:
            continue
        suites += 1
        passed += int(match.group(2))
        failed += int(match.group(3))
        ignored += int(match.group(4))
        filtered += int(match.group(6))
        if int(match.group(2)) + int(match.group(3)) + int(match.group(4)) == 0:
            empty.append(current or "(unknown binary)")

print(f"check-workspace-tests: ran {passed + failed} tests across {suites} binaries "
      f"({passed} passed, {failed} failed, {ignored} ignored, {filtered} filtered out)")
print("check-workspace-tests: not checked here — `frontier_*` (wall-clock ratchets, "
      "run serialized by the frontier step), the z3 differential fuzzes (they compile "
      "to ZERO tests without `--features z3`; CLAUDE.md lists them as a linear-arithmetic "
      "pre-merge gate), and any `#[ignore]`d test")

if empty:
    names = sorted(set(empty))
    # A `src/bin` target with no unit tests legitimately runs zero, so this is
    # information rather than a failure — but an emptied test suite looks exactly
    # the same from the outside (the 15-day inert corpus sweep), so the list is
    # printed instead of being swallowed.
    print(f"check-workspace-tests: {len(names)} binaries ran NO tests (a bin or lib "
          f"without unit tests does this legitimately; a suite emptied by a `cfg` "
          f"looks identical):")
    for name in names[:10]:
        print(f"    {name}")
    if len(names) > 10:
        print(f"    ... and {len(names) - 10} more")

if suites == 0 or passed + failed == 0:
    print("check-workspace-tests: the sweep ran ZERO tests. That is the "
          "'running 0 tests ... ok' failure mode, not a pass.", file=sys.stderr)
    sys.exit(1)
sys.exit(0)
PY
scope_status=$?

if [ "$status" -ne 0 ]; then
  echo "check-workspace-tests: cargo test FAILED (exit $status)" >&2
  exit "$status"
fi
[ "$scope_status" -ne 0 ] && exit "$scope_status"

"$root/scripts/check-source-freshness.sh" --gate test --record
