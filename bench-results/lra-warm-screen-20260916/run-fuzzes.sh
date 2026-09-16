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
# Where a FAILING run's log is kept. A gate that throws away the evidence of its
# own failure can report that something broke and never say what.
KEEP="${2:-$(dirname -- "$OUT")/fuzz-failures}"
SUITES="qf_lra_differential_fuzz simplex_lra_fallback_differential \
        qf_uflra_differential_fuzz difference_logic_differential_fuzz \
        qf_lia_differential_fuzz qf_lra_cube_sequence_differential_fuzz"

: > "$OUT"
fail=0
for arm in off on screened; do
  total=0
  for suite in $SUITES; do
    log="$(mktemp)"
    # Through `cargo-serialized.sh`, not bare cargo: two dev boxes have been
    # taken down by concurrent lane builds here and a kernel OOM killed a live
    # session. Bare cargo in a runner that loops eighteen times is the shape
    # that does it.
    AXEYUM_LRA_WARM_CUBE="$arm" \
      scripts/cargo-serialized.sh test -p axeyum-solver --features z3,full --test "$suite" \
      > "$log" 2>&1
    rc=$?
    # The harness's own count. `grep -c` inside arithmetic is banned here and a
    # bare exit status is what this script exists not to trust.
    line=$(sed -n 's/^test result: .*/&/p' "$log" | tail -1)
    # `\([0-9]*\) passed` WITHOUT anchoring on `ok.` -- this parser read only
    # `ok. N passed`, so a suite that reported `FAILED. 3 passed; 1 failed` came
    # back as n=0 and was then announced as "ZERO TESTS -- compiled to nothing".
    # That is a misdiagnosis with the OPPOSITE remedy: an inert suite needs a
    # feature flag, a failing one needs a fix. It happened on this lane's first
    # run, on `difference_logic_differential_fuzz` in the `on` arm.
    n=$(printf '%s' "$line" | sed -n 's/.*[^0-9]\([0-9][0-9]*\) passed.*/\1/p')
    n="${n:-0}"
    f=$(printf '%s' "$line" | sed -n 's/.*; \([0-9][0-9]*\) failed.*/\1/p')
    f="${f:-0}"
    printf '%-9s %-42s rc=%s tests=%s failed=%s %s\n' \
      "$arm" "$suite" "$rc" "$n" "$f" "${line:-NO-RESULT-LINE}" >> "$OUT"
    # THREE outcomes, not two, because their remedies are disjoint.
    if [ -z "$line" ]; then
      printf '%-9s %-42s NO RESULT LINE -- the run did not happen (build? disk?)\n' \
        "$arm" "$suite" >> "$OUT"
      fail=1
    elif [ "$rc" -ne 0 ] || [ "$f" -ne 0 ]; then
      printf '%-9s %-42s FAILED (%s passed, %s failed) -- log kept at %s\n' \
        "$arm" "$suite" "$n" "$f" "$KEEP/$arm.$suite.log" >> "$OUT"
      # THE FAILING LOG IS KEPT. The first version deleted every log, so this
      # lane's one real failure could not be diagnosed at all -- exactly the
      # defect ADR-2125 section 5.8 had to fix in its own ratchet runner, which
      # "captured the output to a temp file and deleted it, keeping only the
      # count".
      mkdir -p "$KEEP" && cp "$log" "$KEEP/$arm.$suite.log"
      fail=1
    elif [ "$n" -eq 0 ]; then
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
