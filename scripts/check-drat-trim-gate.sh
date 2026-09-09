#!/usr/bin/env bash
# The drat-trim half of the external-checker gates (roadmap item 0.3), and the
# wrapper `just interpolant-certificate` now runs instead of a bare `cargo test`.
#
# TWO THINGS ARE WRONG WITH THE BARE FORM, both measured 2026-09-09.
#
# 1. `AXEYUM_REQUIRE_DRAT_TRIM=1` is honoured by exactly ONE of the THREE
#    drat-trim tests in `crates/axeyum-cnf/tests/propositional_interpolant_
#    certified.rs`. The other two -- including
#    `the_independent_checker_rejects_a_tampered_certificate`, which is the
#    NEGATIVE CONTROL for the external checker -- do
#
#        let Some(bin) = drat_trim() else {
#            eprintln!("SKIP: no drat-trim binary");
#            return;
#        };
#
#    with no assertion at all. So on a host without the binary the recipe that
#    exists to prove a third party accepts our artifact runs its positive test
#    (which fails, correctly) and silently skips the control that would show the
#    checker can say no. This script fails on any `SKIP: no drat-trim` line, so
#    the skip cannot reach a gate whatever the suite does.
#
# 2. Exit status is not the verdict. `references/drat-trim/drat-trim.c` has
#    SEVENTEEN `exit (0)` sites -- note the space; `exit(0)` matches none of
#    them -- covering every `c MEMOUT:` reallocation failure, the parse refusal
#    at `:1065` ("did not find p cnf line in input file"), and
#    `printf ("s TIMEOUT\n"), exit (0);` at `:905`. Measured against the 2026
#    build: a CNF with no `p cnf` header prints an ERROR line and EXITS 0. The
#    suite already reads `s VERIFIED` out of stdout, which is the right
#    discipline; `scripts/tests/test_drat_trim_exit_contract.py` pins it, and
#    this script also fails a run that executed ZERO tests.
#
# Usage:
#   scripts/check-drat-trim-gate.sh     # resolve, require, run, refuse skips
#
# On a machine with no drat-trim at all: AXEYUM_ALLOW_NO_DRAT_TRIM=1, which
# prints, in words, that no external DRAT check ran.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

resolve_drat_trim() {
  if [ -n "${AXEYUM_DRAT_TRIM_BIN:-}" ]; then
    if [ -x "$AXEYUM_DRAT_TRIM_BIN" ]; then
      printf '%s\n' "$AXEYUM_DRAT_TRIM_BIN"
      return 0
    fi
    echo "check-drat-trim-gate: AXEYUM_DRAT_TRIM_BIN=$AXEYUM_DRAT_TRIM_BIN is not executable." >&2
    return 1
  fi
  local vendored="references/drat-trim/drat-trim"
  [ -x "$vendored" ] && printf '%s\n' "$vendored"
}

bin=$(resolve_drat_trim)
if [ -z "$bin" ]; then
  if [ "${AXEYUM_ALLOW_NO_DRAT_TRIM:-}" = "1" ]; then
    echo "check-drat-trim-gate: AXEYUM_ALLOW_NO_DRAT_TRIM=1 -- ZERO external DRAT checks ran." \
         "Nothing in this run establishes that Marijn Heule's checker accepts our certificates." >&2
    exit 0
  fi
  cat >&2 <<'NOBIN'
check-drat-trim-gate: FAILED -- no `drat-trim` binary.

Build it (one C file, seconds):

    scripts/fetch-references.sh
    # or: cd references/drat-trim && \
    #     gcc -std=c99 -D_GNU_SOURCE -DLONGTYPE -O2 -o drat-trim drat-trim.c

...or point at one:  AXEYUM_DRAT_TRIM_BIN=/path/to/drat-trim
...or state that this host has none:  AXEYUM_ALLOW_NO_DRAT_TRIM=1
NOBIN
  exit 1
fi

echo "check-drat-trim-gate: using $bin"
export AXEYUM_DRAT_TRIM_BIN="$bin"
export AXEYUM_REQUIRE_DRAT_TRIM=1

log=$(mktemp) || exit 2
trap 'rm -f "$log"' EXIT

fail=0
if ! cargo test -q -p axeyum-cnf --test propositional_interpolant_certified \
     -- --nocapture >"$log" 2>&1; then
  echo "check-drat-trim-gate: SUITE FAILED" >&2
  tail -60 "$log" >&2
  fail=1
fi

tests=$(sed -n 's/^running \([0-9]*\) test.*/\1/p' "$log" | awk '{s+=$1} END {print s+0}')
skips=$(grep -c 'SKIP: no drat-trim' "$log" 2>/dev/null || true)

if [ "$tests" = "0" ]; then
  echo "check-drat-trim-gate: the suite compiled to ZERO tests -- the" \
       "'running 0 tests ... ok' trap." >&2
  fail=1
fi
if [ "$skips" != "0" ]; then
  echo "check-drat-trim-gate: $skips test(s) printed 'SKIP: no drat-trim' with the binary" \
       "RESOLVED at $bin. Two of the three drat-trim tests in that suite ignore" \
       "AXEYUM_REQUIRE_DRAT_TRIM and skip unconditionally, including the negative control." >&2
  grep -n 'SKIP: no drat-trim' "$log" >&2
  fail=1
fi

[ "$fail" -ne 0 ] && exit 1
echo "check-drat-trim-gate: OK -- $tests test(s), no skips, external checker $bin"
