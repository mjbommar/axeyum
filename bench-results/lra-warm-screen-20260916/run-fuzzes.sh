#!/usr/bin/env bash
# ADR-2132: the six z3 differential fuzzes, in ALL THREE arms of
# `AXEYUM_LRA_WARM_CUBE`.
#
# # Why the harness's own count is parsed
#
# All six suites are `#![cfg(feature = "z3")]` and compile to ZERO tests without
# it, printing "running 0 tests ... ok" and exiting 0 -- the trap that left the
# corpus sweep inert in `hooks/pre-push` for fifteen days. An exit status is
# therefore not evidence that these ran. This parses the harness's own
# `test result:` line and FAILS on a zero count, so the gate's exit status
# depends on the finding rather than on the runner's optimism.
#
# # Why three arms and not one
#
# [ADR-2055]'s rule: a path defaulting `off` is exercised by no gate. `screened`
# will default off too, so it gets the same treatment `on` got in ADR-2125 --
# and it has a way of being inert that `on` does not, since a fuzz instance that
# never crosses 64 builds runs the cold route in all three arms. That is stated
# rather than hidden: `qf_lra_cube_sequence_differential_fuzz` is the only one of
# the six wide enough to reach the offline loop at all, and the screen's own
# coverage rests on it plus `tests/lra_warm_screen_2132.rs`.
#
# Usage: run-fuzzes.sh [out.txt]
set -u
OUT="${1:-fuzz-arms.txt}"
SUITES="qf_lra_differential_fuzz simplex_lra_fallback_differential \
        qf_uflra_differential_fuzz difference_logic_differential_fuzz \
        qf_lia_differential_fuzz qf_lra_cube_sequence_differential_fuzz"

: > "$OUT"
fail=0
for arm in off on screened; do
  total=0
  for suite in $SUITES; do
    log="$(mktemp)"
    AXEYUM_LRA_WARM_CUBE="$arm" \
      cargo test -p axeyum-solver --features z3,full --test "$suite" \
      > "$log" 2>&1
    rc=$?
    # The harness's own count. `grep -c` inside arithmetic is banned here and a
    # bare exit status is what this script exists not to trust.
    line=$(sed -n 's/^test result: .*/&/p' "$log" | tail -1)
    n=$(printf '%s' "$line" | sed -n 's/.*ok\. \([0-9]*\) passed.*/\1/p')
    n="${n:-0}"
    printf '%-9s %-42s rc=%s tests=%s %s\n' "$arm" "$suite" "$rc" "$n" "${line:-NO-RESULT-LINE}" >> "$OUT"
    if [ "$rc" -ne 0 ]; then fail=1; fi
    if [ "$n" -eq 0 ]; then
      printf '%-9s %-42s ZERO TESTS -- the suite compiled to nothing\n' "$arm" "$suite" >> "$OUT"
      fail=1
    fi
    total=$((total + n))
    rm -f "$log"
  done
  printf '%-9s TOTAL tests=%s\n' "$arm" "$total" >> "$OUT"
done

cat "$OUT"
if [ "$fail" -ne 0 ]; then echo "FUZZ ARMS: FAILED"; exit 1; fi
echo "FUZZ ARMS: all suites green with a nonzero count in all three arms"
