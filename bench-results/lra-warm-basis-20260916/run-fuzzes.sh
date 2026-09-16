#!/usr/bin/env bash
# ADR-2125: the z3 differential fuzzes, in BOTH arms of the lever.
#
# # Why both arms
#
# A lever that ships `off` leaves the new path exercised by nothing. Running the
# fuzzes only in the default arm would be a gate that structurally cannot see
# this change -- they would pass identically with the warm cube decider deleted.
# So every suite runs again with `AXEYUM_LRA_WARM_CUBE=on`, which is the arm
# where the soundness risk actually lives.
#
# # Why a test COUNT is checked and not just the exit status
#
# All six suites are `#![cfg(feature = "z3")]` and compile to ZERO tests without
# it, printing "running 0 tests ... ok" and exiting 0. That trap left the corpus
# sweep inert in `hooks/pre-push` for 15 days. This script therefore parses the
# `test result:` line and FAILS on a zero count, so a green run cannot be a run
# that compiled nothing.
#
# The sixth suite is this lane's own: the other five generate 2-5 atoms and the
# online engine admits 1,024, so they cannot reach the offline cube loop at all.
#
# Usage: run-fuzzes.sh            (from the repository root)
set -u

SUITES="qf_lra_differential_fuzz simplex_lra_fallback_differential \
        qf_uflra_differential_fuzz difference_logic_differential_fuzz \
        qf_lia_differential_fuzz qf_lra_cube_sequence_differential_fuzz"

fail=0
printf '%-44s %-6s %-6s %s\n' suite arm tests result
for arm in off on; do
  for suite in $SUITES; do
    log="$(mktemp)"
    AXEYUM_LRA_WARM_CUBE="$arm" \
      scripts/cargo-serialized.sh test -p axeyum-solver --features z3 \
      --test "$suite" > "$log" 2>&1
    rc=$?
    # The COUNT, from the harness's own summary line. `grep -c` is deliberately
    # not used in arithmetic here; this reads the number the harness printed.
    n=$(sed -n 's/^test result: .* \([0-9][0-9]*\) passed.*/\1/p' "$log" | head -1)
    n="${n:-0}"
    verdict=ok
    if [ "$rc" -ne 0 ]; then verdict="FAILED rc=$rc"; fail=1; fi
    if [ "$n" = "0" ]; then verdict="INERT (0 tests) -- not evidence"; fail=1; fi
    printf '%-44s %-6s %-6s %s\n' "$suite" "$arm" "$n" "$verdict"
    [ "$verdict" = "ok" ] || cat "$log" | tail -25
    rm -f "$log"
  done
done

if [ "$fail" -ne 0 ]; then
  echo "FUZZ GATE FAILED"
  exit 1
fi
echo "FUZZ GATE PASSED: every suite green in both arms, every count nonzero"
