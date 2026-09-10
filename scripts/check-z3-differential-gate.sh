#!/usr/bin/env bash
# Real-Z3 differential gate: run every suite that adjudicates our verdicts
# against the SYSTEM Z3 BINARY, and report how many of them actually had an
# adjudicator.
#
# Why this exists, in one measurement.
#
# Thirteen files under `crates/axeyum-solver/tests/` hardcoded
# `const Z3_BIN: &str = "/usr/bin/z3"` and, when that path was absent, printed a
# note to stderr and `return`ed -- a PASSING test. One said so in words:
#
#     // Probe the Z3 binary once; if absent, the differential is impossible and
#     // the test is a no-op pass (mirrors the other fuzzers' adjudication-
#     // neutral skip).
#
# These suites are the ONLY checks in this repository that compare our verdicts
# against an independent solver. `AXEYUM_REQUIRE_LEAN`, `AXEYUM_REQUIRE_ABC` and
# `AXEYUM_REQUIRE_CARCARA` all already make an absent binary a FAILURE; there was
# no `AXEYUM_REQUIRE_Z3`. On a host without Z3 -- and `docs/contributor-guide/
# fleet-hosts.md` never recorded which hosts those are -- every one of these
# suites was green and empty, and nothing said so.
#
# So this gate does three things a bare `cargo test` cannot:
#
#   1. RESOLVES the binary and prints its version, so a result names its oracle.
#   2. Sets `AXEYUM_REQUIRE_Z3=1`, so a suite that cannot find Z3 FAILS instead
#      of printing a skip note and passing. A machine that genuinely has no Z3
#      sets `AXEYUM_ALLOW_NO_Z3=1` and gets a banner saying, in words, that ZERO
#      independent-solver comparisons ran.
#   3. FAILS a suite that ran ZERO tests. `--features full,z3` is mandatory on
#      these targets (`#![cfg(feature = "full")]` plus `#[cfg(feature = "z3")]`
#      fronts) and a missing flag compiles a binary that prints
#      "running 0 tests ... ok" and exits 0. That is the same defect wearing a
#      different hat, and this repository has shipped it before (the corpus
#      sweep was inert in `hooks/pre-push` for 15 days).
#
# Usage:
#   scripts/check-z3-differential-gate.sh              # resolve, require, count
#   scripts/check-z3-differential-gate.sh --self-check # the gate's own negative
#                                                      # control (fast)
#   scripts/check-z3-differential-gate.sh --list       # print the suite list
#   scripts/check-z3-differential-gate.sh --print-bin  # resolve, run nothing
#
# `--self-check` re-runs ONE suite with `AXEYUM_Z3_BIN` pointed at a path that
# does not exist and REQUIRES it to fail. It is the answer to "delete one guard
# and require that exactly one test dies": remove the `assert!(!z3_required())`
# from `crates/axeyum-solver/tests/common_z3/mod.rs` and `--self-check` fails.
# It is cheap -- an absent oracle is detected before any fuzzing starts.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

# Every suite that shells SMT-LIB text at the system Z3 binary. Derived, not
# remembered: `--list` prints this, and `--check-list` re-derives it from the
# source tree and fails if the two disagree, so a new differential suite cannot
# be added without either joining this gate or being noticed.
#
# package|features|target
SUITES="\
axeyum-solver|full,z3|fp_differential_fuzz
axeyum-solver|full,z3|online_string_front_door_fuzz
axeyum-solver|full,z3|qf_nia_iand_differential_fuzz
axeyum-solver|full,z3|qf_nia_pow2_differential_fuzz
axeyum-solver|full,z3|qf_s_online_differential_fuzz
axeyum-solver|full,z3|qf_s_online_membership_differential_fuzz
axeyum-solver|full,z3|qf_s_replace_fold_differential_fuzz
axeyum-solver|full,z3|qf_slia_length_lia_differential_fuzz
axeyum-solver|full,z3|qf_slia_lex_order_differential_fuzz
axeyum-solver|full,z3|regex_membership_differential_fuzz
axeyum-solver|full,z3|seq_differential_fuzz
axeyum-solver|full,z3|string_differential_fuzz
axeyum-solver|full,z3|word_equation_differential_fuzz"

# The suite used by --self-check. The cheapest one to reach its Z3 probe.
SELF_CHECK_SUITE="qf_nia_iand_differential_fuzz"
SELF_CHECK_FEATURES="full,z3"

# ---------------------------------------------------------------------------
# Binary resolution
# ---------------------------------------------------------------------------
DEFAULT_Z3_BIN="/usr/bin/z3"

resolve_z3() {
  local candidate="${AXEYUM_Z3_BIN:-$DEFAULT_Z3_BIN}"
  if "$candidate" --version >/dev/null 2>&1; then
    printf '%s\n' "$candidate"
    return 0
  fi
  return 1
}

if [ "${1:-}" = "--list" ]; then
  printf '%s\n' "$SUITES"
  exit 0
fi

# `--check-list`: the suite list above must equal the set of test files that
# actually reference the shared probe. A gate whose subject list is a literal is
# a gate on the maintainer's memory.
if [ "${1:-}" = "--check-list" ]; then
  derived=$(grep -l 'common_z3::z3_available' crates/axeyum-solver/tests/*.rs |
    xargs -r -n1 basename | sed 's/\.rs$//' | LC_ALL=C sort)
  listed=$(printf '%s\n' "$SUITES" | cut -d'|' -f3 | LC_ALL=C sort)
  if [ "$derived" != "$listed" ]; then
    echo "check-z3-differential-gate --check-list: the suite list is stale." >&2
    diff <(printf '%s\n' "$listed") <(printf '%s\n' "$derived") >&2
    exit 1
  fi
  count=$(printf '%s\n' "$listed" | grep -c .)
  echo "check-z3-differential-gate --check-list: OK -- $count suite(s), list matches the tree."
  exit 0
fi

z3=$(resolve_z3)
if [ -z "$z3" ]; then
  if [ "${AXEYUM_ALLOW_NO_Z3:-}" = "1" ]; then
    echo "check-z3-differential-gate: AXEYUM_ALLOW_NO_Z3=1 -- ZERO independent-solver" \
      "comparisons ran. Nothing in this run establishes that our verdicts agree with" \
      "any solver but our own." >&2
    exit 0
  fi
  cat >&2 <<'NOBIN'
check-z3-differential-gate: FAILED -- no usable Z3 binary.

This is a FAILURE and not a skip on purpose. Until 2026-09-10 every suite in this
gate returned early and PASSED when the binary was absent, so an absent Z3 looked
exactly like a Z3 that agreed with our verdict on every generated script. These
are the only checks in the repository that compare us against an independent
solver.

To fix, install it:      apt-get install z3
...or point at one:      AXEYUM_Z3_BIN=/path/to/z3
...or state, deliberately, that this host has none and that therefore no
independent adjudication ran:   AXEYUM_ALLOW_NO_Z3=1
NOBIN
  exit 1
fi

z3_version=$("$z3" --version 2>&1 | head -1)
z3_real=$(readlink -f "$z3" 2>/dev/null || printf '%s' "$z3")

if [ "${1:-}" = "--print-bin" ]; then
  printf '%s\t%s\t%s\n' "$z3" "$z3_real" "$z3_version"
  exit 0
fi

# ---------------------------------------------------------------------------
# --self-check: the gate's own negative control.
# ---------------------------------------------------------------------------
#
# Point AXEYUM_Z3_BIN at a path that does not exist and require the suite to
# FAIL under AXEYUM_REQUIRE_Z3=1 and to PASS with it unset. Both halves matter:
# the first is the guard this whole change exists to add; the second is the
# promise that an ordinary developer run on a Z3-less host is unaffected.
if [ "${1:-}" = "--self-check" ]; then
  missing="/nonexistent/axeyum-self-check-z3-$$"
  self_fail=0
  scratch=$(mktemp -d) || exit 2
  trap 'rm -rf "$scratch"' EXIT

  echo "check-z3-differential-gate --self-check: suite $SELF_CHECK_SUITE," \
    "AXEYUM_Z3_BIN=$missing"

  # (a) REQUIRED + absent -> must FAIL.
  if AXEYUM_Z3_BIN="$missing" AXEYUM_REQUIRE_Z3=1 \
    cargo test -q -p axeyum-solver --features "$SELF_CHECK_FEATURES" \
    --test "$SELF_CHECK_SUITE" -- --nocapture >"$scratch/required.log" 2>&1; then
    echo "check-z3-differential-gate --self-check: FAILED -- $SELF_CHECK_SUITE PASSED with" \
      "AXEYUM_REQUIRE_Z3=1 and no Z3 binary. The guard in tests/common_z3/mod.rs is not" \
      "firing, and this gate cannot detect an absent oracle." >&2
    tail -30 "$scratch/required.log" >&2
    self_fail=1
  else
    echo "check-z3-differential-gate --self-check: REQUIRED + absent -> suite failed (correct)"
  fi

  # (b) NOT required + absent -> must PASS, and must say so.
  if ! AXEYUM_Z3_BIN="$missing" \
    cargo test -q -p axeyum-solver --features "$SELF_CHECK_FEATURES" \
    --test "$SELF_CHECK_SUITE" -- --nocapture >"$scratch/default.log" 2>&1; then
    echo "check-z3-differential-gate --self-check: FAILED -- $SELF_CHECK_SUITE failed with" \
      "AXEYUM_REQUIRE_Z3 unset and no Z3 binary. The default must stay a skip." >&2
    tail -30 "$scratch/default.log" >&2
    self_fail=1
  elif [ "$(grep -c 'AXEYUM-Z3-SKIPPED' "$scratch/default.log")" = "0" ]; then
    echo "check-z3-differential-gate --self-check: FAILED -- $SELF_CHECK_SUITE passed with no" \
      "Z3 and printed no AXEYUM-Z3-SKIPPED line. A silent skip is the defect." >&2
    self_fail=1
  else
    echo "check-z3-differential-gate --self-check: default + absent -> suite passed and printed" \
      "AXEYUM-Z3-SKIPPED (correct)"
  fi

  if [ "$self_fail" -ne 0 ]; then
    echo "check-z3-differential-gate --self-check: FAILED" >&2
    exit 1
  fi
  echo "check-z3-differential-gate --self-check: OK"
  exit 0
fi

# ---------------------------------------------------------------------------
# The gate proper.
# ---------------------------------------------------------------------------
export AXEYUM_Z3_BIN="$z3"
export AXEYUM_REQUIRE_Z3=1

echo "check-z3-differential-gate: using $z3_version ($z3)"

scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT

fail=0
failed_suites=()
total_tests=0
suite_count=0

while IFS='|' read -r package features target; do
  [ -n "$target" ] || continue
  suite_count=$((suite_count + 1))
  log="$scratch/$target.log"
  args=(test -q -p "$package")
  [ -n "$features" ] && args+=(--features "$features")
  args+=(--test "$target" -- --nocapture)
  if ! cargo "${args[@]}" >"$log" 2>&1; then
    echo "check-z3-differential-gate: SUITE FAILED: $package/$target" >&2
    tail -60 "$log" >&2
    failed_suites+=("$target")
    fail=1
  fi

  ran=$(grep -c '^running [0-9]* test' "$log" 2>/dev/null || true)
  tests=$(sed -n 's/^running \([0-9]*\) test.*/\1/p' "$log" | awk '{s+=$1} END {print s+0}')
  skipped=$(grep -c 'AXEYUM-Z3-SKIPPED' "$log" 2>/dev/null || true)
  # WHICH binary did the suite use? Exporting AXEYUM_Z3_BIN is an instruction,
  # not evidence; the suite prints one banner naming what it resolved.
  used_bins=$(sed -n 's/.*AXEYUM-Z3-BIN bin=\(.*\) version=.*/\1/p' "$log" | LC_ALL=C sort -u)

  total_tests=$((total_tests + tests))

  if [ "$ran" = "0" ] || [ "$tests" = "0" ]; then
    echo "check-z3-differential-gate: $target compiled to ZERO tests -- the" \
      "'running 0 tests ... ok' trap. These targets need --features full,z3." >&2
    failed_suites+=("$target(0-tests)")
    fail=1
  fi
  if [ "$skipped" != "0" ]; then
    echo "check-z3-differential-gate: $target printed AXEYUM-Z3-SKIPPED under" \
      "AXEYUM_REQUIRE_Z3=1; a skip must never reach this gate." >&2
    grep 'AXEYUM-Z3-SKIPPED' "$log" >&2
    failed_suites+=("$target(skipped)")
    fail=1
  fi
  if [ -z "$used_bins" ]; then
    echo "check-z3-differential-gate: $target ran $tests test(s) but printed no" \
      "AXEYUM-Z3-BIN banner, so which oracle produced them is unknown. A result that" \
      "does not name its oracle is not evidence." >&2
    failed_suites+=("$target(unnamed-oracle)")
    fail=1
  else
    while IFS= read -r used; do
      [ -n "$used" ] || continue
      used_real=$(readlink -f "$used" 2>/dev/null || printf '%s' "$used")
      if [ "$used_real" != "$z3_real" ]; then
        echo "check-z3-differential-gate: $target used $used, not the resolved $z3." >&2
        failed_suites+=("$target(wrong-binary)")
        fail=1
      fi
    done <<<"$used_bins"
  fi
  printf 'check-z3-differential-gate: %-44s %3s test(s), oracle=%s\n' \
    "$target" "$tests" "${used_bins:-NONE}"
done <<<"$SUITES"

echo "check-z3-differential-gate: $suite_count suite(s), $total_tests test(s) adjudicated" \
  "against $z3_version"

if [ "$fail" -ne 0 ]; then
  [ ${#failed_suites[@]} -gt 0 ] &&
    printf 'check-z3-differential-gate: FAILED: %s\n' "${failed_suites[*]}" >&2
  exit 1
fi
echo "check-z3-differential-gate: OK -- every suite found its oracle and none skipped."
