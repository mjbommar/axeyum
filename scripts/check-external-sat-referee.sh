#!/usr/bin/env bash
# Gate for the EXTERNAL SAT referee (ADR-1910):
# `crates/axeyum-cnf/tests/external_sat_referee.rs`.
#
# The referee this replaces (`--features batsat-reference`,
# `tests/native_vs_batsat_differential.rs`) was measured on 2026-09-10 to be in
# NO gate, CI job, `justfile` recipe or git hook. It ran only when a human ran
# it, which is to say it provided zero automatic assurance. That failure mode is
# what this script exists to prevent for its replacement: the test file is
# ungated Rust, and this wrapper is what puts it on an automatic path AND makes
# the exit status depend on the finding rather than on `cargo`'s exit code.
#
# Three things the bare `cargo test` line cannot do, and this script does:
#
#   1. Resolve the binary ITSELF, so an absent referee is a VISIBLE SKIP line in
#      the aggregate gate's output rather than four tests that print a banner and
#      return ok. `cargo test` cannot express "skipped".
#   2. Re-derive the finding from the test's own `compared=N` output instead of
#      trusting `test result: ok`. A test that adjudicated nothing and a test
#      that adjudicated 524 instances exit identically; the count is the
#      discriminator. The test asserts `compared > 0` internally too -- this is
#      the independent second reading, because a guard inside the subject is not
#      a guard on the subject.
#   3. Assert a NONZERO TEST COUNT. This file is not feature-gated today, but
#      `--test <name>` prints "running 0 tests ... ok" and exits 0 the moment a
#      `#![cfg(...)]` appears at its top, which is exactly how a corpus gate here
#      stayed inert for fifteen days while looking green.
#
# Usage:
#   scripts/check-external-sat-referee.sh
#     Runs the referee if a binary is present; prints a loud SKIP and exits 0 if
#     not.
#   AXEYUM_REQUIRE_EXTERNAL_SAT=1 scripts/check-external-sat-referee.sh
#     An absent binary is a FAILURE. Use this in any lane that publishes a
#     soundness claim about the SAT core.
#
# Provision the binary with `scripts/provision-external-sat-referee.sh`.

set -uo pipefail

cd "$(dirname "$0")/.."

# Ratchet, not a pin: raise it when tests are added, never lower it silently.
# 4 as of 2026-09-10 (ADR-1910): micro-cnf corpus, seeded random 3-SAT at the
# threshold ratio, degenerate formulas, and the known-verdict negative control.
MIN_TESTS=4

# Floor on the (instance, referee, native-arm) triples actually adjudicated.
# Measured 2026-09-10 with cadical 3.0.1 AND kissat 4.0.4 present: 524.
# With ONE referee it halves, so the floor sits below that -- it is here to
# catch a population that collapsed to nothing, not to pin a host's toolchain.
MIN_COMPARED=100

# Resolve a referee exactly as the test does, so the SKIP decision and the test's
# own decision cannot disagree. `command -v` on the bare name covers PATH.
resolve() {
  local name="$1" override="$2" candidate
  if [ -n "${!override:-}" ]; then
    candidate="${!override}"
  elif command -v "$name" >/dev/null 2>&1; then
    candidate="$name"
  elif [ -x "$HOME/.local/bin/$name" ]; then
    candidate="$HOME/.local/bin/$name"
  else
    return 1
  fi
  "$candidate" --version >/dev/null 2>&1 || return 1
  printf '%s\n' "$candidate"
}

found=()
if bin="$(resolve cadical AXEYUM_CADICAL_BIN)"; then found+=("cadical=$bin"); fi
if bin="$(resolve kissat AXEYUM_KISSAT_BIN)"; then found+=("kissat=$bin"); fi

if [ ${#found[@]} -eq 0 ]; then
  if [ "${AXEYUM_REQUIRE_EXTERNAL_SAT:-}" = "1" ]; then
    echo "external-sat-referee: FAIL -- AXEYUM_REQUIRE_EXTERNAL_SAT=1 and no" \
         "cadical/kissat binary was found. Run scripts/provision-external-sat-referee.sh" >&2
    exit 1
  fi
  # As loud as check.sh's own TIMED OUT banner, and for the same reason: a step
  # that did not run was NOT checked, and a reader skimming the summary must not
  # be able to mistake it for one that passed.
  echo "external-sat-referee: SKIPPED -- no external SAT binary (cadical, kissat)." >&2
  echo "external-sat-referee: THE NATIVE CORE'S VERDICTS WERE NOT ADJUDICATED BY ANY" \
       "THIRD PARTY ON THIS RUN. This is not evidence of agreement." >&2
  echo "external-sat-referee: provision with scripts/provision-external-sat-referee.sh," \
       "or set AXEYUM_REQUIRE_EXTERNAL_SAT=1 to make absence a failure." >&2
  exit 0
fi

echo "external-sat-referee: referees ${found[*]}"

# `--nocapture` is LOAD-BEARING: the `compared=N` lines are `println!` from
# inside the tests and are swallowed without it, which would leave this script
# with nothing but the exit status to read -- the very thing it exists not to
# trust. `--test-threads=1` keeps the lines and the test names interleaved in a
# readable order; the whole suite is ~1.5 s, so serialising costs nothing.
out="$(scripts/cargo-serialized.sh test -p axeyum-cnf --test external_sat_referee \
  -- --nocapture --test-threads=1 2>&1)"
status=$?

if [ "$status" -ne 0 ]; then
  echo "external-sat-referee: FAIL (cargo status $status)" >&2
  printf '%s\n' "$out" | tail -60 >&2
  exit 1
fi

# `tail`, never `head` -- head SIGPIPEs the producer (CLAUDE.md banned idiom).
tests="$(printf '%s\n' "$out" \
  | sed -n 's/^test result: ok\. \([0-9][0-9]*\) passed.*/\1/p' | tail -1)"
if [ -z "$tests" ] || [ "$tests" -lt "$MIN_TESTS" ]; then
  echo "external-sat-referee: FAIL -- ran ${tests:-no} tests, expected at least" \
       "$MIN_TESTS. A feature gate or a rename has emptied this suite; it is" \
       "inert, not passing." >&2
  printf '%s\n' "$out" | tail -30 >&2
  exit 1
fi

# Re-derive the adjudicated count from the test's own reports and sum it. `grep
# -c` first so an empty result is distinguishable from a zero sum.
# NOT anchored with `^`. Under `--test-threads=1 --nocapture` libtest prints the
# test's stdout on the SAME line it opened with `test <name> ... `, so an
# anchored pattern matches zero lines while the suite is perfectly healthy --
# which is exactly what this guard reported on its first run. The guard was
# right about its own wiring; the anchor was the bug.
reports="$(printf '%s\n' "$out" | grep -cE 'external-sat-referee: compared=[0-9]+')"
if [ "$reports" -eq 0 ]; then
  echo "external-sat-referee: FAIL -- the suite passed but emitted NO" \
       "'compared=' report. Either --nocapture was dropped or the tests no" \
       "longer report what they adjudicated; in both cases this gate is" \
       "measuring nothing." >&2
  printf '%s\n' "$out" | tail -30 >&2
  exit 1
fi
compared="$(printf '%s\n' "$out" \
  | sed -n 's/.*external-sat-referee: compared=\([0-9][0-9]*\).*/\1/p' \
  | awk '{ total += $1 } END { print total + 0 }')"

if [ "$compared" -lt "$MIN_COMPARED" ]; then
  echo "external-sat-referee: FAIL -- only $compared comparisons were adjudicated" \
       "across $reports reports, below the floor of $MIN_COMPARED. The suite is" \
       "green because it compared almost nothing." >&2
  printf '%s\n' "$out" | grep -E 'external-sat-referee:' >&2
  exit 1
fi

printf '%s\n' "$out" | grep -E -o 'external-sat-referee: compared=.*'
echo "external-sat-referee: OK -- $tests tests, $compared adjudicated comparisons" \
     "against ${found[*]}"
