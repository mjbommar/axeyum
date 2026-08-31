#!/usr/bin/env bash
# Gate for the number-theory certificate checkers (`axeyum_cas::ntheory_certify`).
#
# Runs the adversarial fixture suite and ASSERTS A NONZERO, RATCHETED TEST
# COUNT. A bare `cargo test -p axeyum-cas --lib ntheory_certify` exits 0 when
# the filter matches nothing -- if the module is renamed or the test submodule
# is dropped, the gate goes green having checked no forgery at all. That is the
# exact green-looking-nothing this repository has shipped before (a corpus gate
# inert for 15 days, a capability ratchet documented without its feature flag),
# so the count is the discriminator, not the exit status alone.
#
# The MUTATION sweep that measures whether each guard is load-bearing is
# `scripts/tests/test-ntheory-certificate-guards.sh`. It runs ~23 incremental
# builds and is deliberately NOT wired into the aggregate gate; run it whenever
# a guard is added, removed, or reworded.
#
# Usage: scripts/check-ntheory-certificates.sh

set -uo pipefail

cd "$(dirname "$0")/.."

# Ratchet, not a pin: raise it when tests are added, never lower it silently.
# 33 -> 34 (2026-08-31, ADR-1055): added independent_gcd_lcm_agree_with_ntheory,
# pinning that the new checker_gcd/checker_lcm (added so check_crt_certificate
# no longer calls ntheory::gcd/ntheory::lcm directly) agree with ntheory's.
MIN_TESTS=34

out="$(scripts/cargo-serialized.sh test -p axeyum-cas --lib ntheory_certify 2>&1)"
status=$?

# `tail`, never `head` -- head SIGPIPEs the producer (CLAUDE.md banned-idiom 2).
count="$(printf '%s\n' "$out" \
  | sed -n 's/^test result: ok\. \([0-9][0-9]*\) passed.*/\1/p' | tail -1)"

if [ "$status" -ne 0 ]; then
  echo "ntheory-certificates: FAIL (cargo status $status)"
  printf '%s\n' "$out" | tail -30
  exit 1
fi

if [ -z "${count:-}" ]; then
  echo "ntheory-certificates: FAIL -- could not read a test count from the harness"
  printf '%s\n' "$out" | tail -10
  exit 1
fi

if [ "$count" -lt "$MIN_TESTS" ]; then
  echo "ntheory-certificates: FAIL -- $count tests ran, expected at least $MIN_TESTS"
  echo "  A shrinking count means fixtures were dropped or the filter stopped matching."
  exit 1
fi

echo "ntheory-certificates: OK -- $count adversarial fixtures passed (floor $MIN_TESTS)"
