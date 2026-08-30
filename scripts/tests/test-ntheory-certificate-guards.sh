#!/usr/bin/env bash
# Mutation controls for `axeyum_cas::ntheory_certify`.
#
# Deletes each guard in the four certificate checkers -- one at a time, by
# rewriting its condition to a constant that makes it never fire -- and records
# which tests die. A guard whose deletion kills NOTHING is a guard the suite
# does not measure, which in a certificate checker means an accepted forgery.
#
# This COMPLEMENTS and does not replace the adversarial fixtures in
# `ntheory_certify/ntheory_certify_tests.rs`: mutation measures the guards that
# EXIST and cannot find a distinction the certificate format fails to record
# (see the `nra_monomial_bound_cert` retrospective in CLAUDE.md, where nine
# guards were each killed by exactly one test and the module was still
# unsound). Both are needed, and the fixtures are the load-bearing half.
#
# Not in the table, deliberately:
#   R5 (`residues.get(left)` / `.get(right)`) is a total-function construction,
#   not a deletable guard -- removing it is an index that panics rather than a
#   check that stops firing, so a mutant would measure Rust, not the suite. The
#   `forged_crt_rejects_out_of_range_conflict_indices` test pins that
#   out-of-range indices return false instead of panicking.
#
# Usage:
#   scripts/tests/test-ntheory-certificate-guards.sh          # full sweep
#   scripts/tests/test-ntheory-certificate-guards.sh --list   # guard names
#
# Exit 0 when the survivor set equals the two documented resource guards; exit 1
# naming any new survivor, any expected survivor that started dying, or any
# mutant that could not be measured. ~23 incremental builds; NOT a fast gate.

set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SUBJECT="$REPO_ROOT/crates/axeyum-cas/src/ntheory_certify.rs"

# Each row: NAME<TAB>ORIGINAL<TAB>MUTANT.
# ORIGINAL must occur EXACTLY ONCE in the subject. The harness asserts that, so
# a guard that is later reworded is reported as NOT MEASURED rather than
# silently skipped -- the failure mode this whole script exists to prevent.
read -r -d '' MUTATIONS <<'TABLE'
G1-subject-range	if n < 2 {	if false {
G2-witness-range	if cert.witness <= 0 || cert.witness >= n {	if false {
G3-subcert-arity	if cert.factors.len() != cert.subcerts.len() {	if false {
G4-ascending-bases	if window[0].0 >= window[1].0 {	if false {
G5-exponent-and-base	.any(|&(base, exponent)| exponent == 0 || base < 2)	.any(|&(base, exponent)| { let _ = (base, exponent); false })
G6-factorization-complete	if product != target {	if false {
G7-recursive-primality	if !check_primality_certificate_at(base, sub, depth + 1) {	if false && !check_primality_certificate_at(base, sub, depth + 1) {
G8-fermat	if pow_mod(witness, target, modulus) != 1 % modulus {	if false {
G9-order-maximality	if pow_mod(witness, target / q, modulus) == 1 % modulus {	if false {
G10-depth-bound	if depth >= MAX_PRATT_DEPTH {	if false {
C1-divisor-lower	if cert.divisor <= 1 {	if false {
C2-divisor-upper	if cert.divisor >= n {	if false {
C3-divides	n % cert.divisor == 0	{ let _ = n % cert.divisor; true }
F1-primality-arity	if cert.factors.len() != cert.primality.len() {	if false {
F2-ascending-factor-bases	if pair[0].0 >= pair[1].0 {	if false {
F3-nonzero-exponent	if cert.factors.iter().any(|&(_, exponent)| exponent == 0) {	if false {
F4-product-identity	if product != n.unsigned_abs() {	if false {
F5-per-factor-primality	.all(|(&(base, _), sub)| check_primality_certificate(base, sub))	.all(|(&(base, _), sub)| { let _ = (base, sub); true })
R1-positive-moduli	if residues.iter().any(|&(_, modulus)| modulus <= 0) {	if false {
R2-canonical-solution	if modulus <= 0 || solution < 0 || solution >= modulus {	if false {
R3-congruences-hold	.any(|&(residue, m)| (solution - residue).rem_euclid(m) != 0)	.any(|&(residue, m)| { let _ = (solution - residue).rem_euclid(m); false })
R4-modulus-is-least	acc == modulus	{ let _ = (acc, modulus); true }
R6-conflict-is-real	(a_left - a_right).rem_euclid(common) != 0	{ let _ = (a_left - a_right).rem_euclid(common); true }
TABLE

if [ "${1:-}" = "--list" ]; then
  printf '%s\n' "$MUTATIONS" | cut -f1
  exit 0
fi

BACKUP="$(mktemp -t ntheory_certify.XXXXXX.rs)"
cp "$SUBJECT" "$BACKUP"
restore() { cp "$BACKUP" "$SUBJECT"; rm -f "$BACKUP"; }
trap restore EXIT INT TERM

run_suite() {
  # Prints the harness output; returns cargo's status. Never a pipeline, so
  # `$?` is this command's own status (CLAUDE.md banned-idiom 1).
  ( cd "$REPO_ROOT" && scripts/cargo-serialized.sh test -p axeyum-cas \
      --lib ntheory_certify 2>&1 )
}

# Read the PASSING count with `tail`, never `head` -- `head` closes the pipe and
# SIGPIPEs the producer (CLAUDE.md banned-idiom 2).
passing_count() {
  printf '%s\n' "$1" | sed -n 's/^test result: ok\. \([0-9][0-9]*\) passed.*/\1/p' | tail -1
}

# Named dead tests, from the summary block cargo prints after `failures:`.
dead_tests() {
  printf '%s\n' "$1" | /usr/bin/grep -E '^    ntheory_certify::' | sort -u
}

baseline_out="$(run_suite)"
baseline_status=$?
baseline_count="$(passing_count "$baseline_out")"
if [ "$baseline_status" -ne 0 ] || [ -z "${baseline_count:-}" ] || [ "$baseline_count" -eq 0 ]; then
  echo "BASELINE FAILED (status=$baseline_status count=${baseline_count:-none}) -- refusing to measure"
  printf '%s\n' "$baseline_out" | tail -20
  exit 1
fi
echo "baseline: $baseline_count tests passing"
echo

survivors=0
measured=0
not_measured=0
survivor_names=""
while IFS=$'\t' read -r name original mutant; do
  [ -z "${name:-}" ] && continue

  occurrences="$(/usr/bin/grep -cF -- "$original" "$SUBJECT")"
  if [ "$occurrences" -ne 1 ]; then
    echo "!! $name: pattern occurs $occurrences times, expected 1 -- NOT MEASURED"
    not_measured=$((not_measured + 1))
    continue
  fi

  python3 - "$SUBJECT" "$original" "$mutant" <<'PY'
import sys
path, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(path).read()
assert text.count(old) == 1, "uniqueness re-checked in python"
open(path, 'w').write(text.replace(old, new))
PY

  out="$(run_suite)"
  status=$?
  cp "$BACKUP" "$SUBJECT"
  measured=$((measured + 1))

  dead="$(dead_tests "$out")"
  n_dead="$(printf '%s\n' "$dead" | /usr/bin/grep -c .)"

  if [ "$status" -eq 0 ]; then
    echo "SURVIVED  $name -- no test died"
    survivors=$((survivors + 1))
    survivor_names="$survivor_names $name"
  elif [ "$n_dead" -eq 0 ]; then
    # A nonzero status with nothing named means the mutant did not compile,
    # which measures nothing about the suite.
    echo "!! $name: mutant did not build -- NOT MEASURED"
    printf '%s\n' "$out" | /usr/bin/grep -E '^error' | sed 's/^/      /' | sed -n '1,3p'
    not_measured=$((not_measured + 1))
  else
    echo "killed by $n_dead: $name"
    printf '%s\n' "$dead" | sed 's/^ *ntheory_certify::ntheory_certify_tests:://' | sed 's/^/      /'
  fi
done <<< "$MUTATIONS"

echo
# Two-way assertion. A guard that survives is one this suite does not measure,
# which in a certificate checker means an accepted forgery -- UNLESS it is a
# resource or defence-in-depth guard that provably cannot change a verdict.
# Exactly three are, and all three were found BY THIS SWEEP rather than by
# design -- which is the whole reason it exists:
#
#   G1-subject-range      every `n < 2` is already excluded by arithmetic: for
#                         `n <= 0` the `u128::try_from(n - 1)` in G6 fails, and
#                         for `n = 1` the target is 0 while a product of bases
#                         `>= 2` (G5) is never 0.
#   G5-exponent-and-base  zero exponents are refuted by G9 and sub-two bases by
#                         G7; G5 alone bounds `checked_prod_pow`, which spins up
#                         to 4.29e9 times at base 0 or 1.
#   G10-depth-bound       a chain deep enough to matter is refuted by G8/G9 at
#                         the top level either way; the bound only stops the
#                         recursion from exhausting the stack first.
#
# All three are retained: a guard only ever rejects more, never less, so it
# cannot make the checker accept a forgery. What is NOT acceptable is leaving
# the redundancy implied, because an unkillable guard reads as coverage it does
# not provide -- so each is documented at its site and pinned here.
#
# Both directions matter. A NEW survivor is an unmeasured guard. An expected
# survivor that starts dying means it became verdict-bearing and its reasoning
# above is stale. Either way this exits 1.
EXPECTED_SURVIVORS="G1-subject-range G5-exponent-and-base G10-depth-bound"
expected_sorted="$(printf '%s\n' $EXPECTED_SURVIVORS | sort | tr '\n' ' ')"
actual_sorted="$(printf '%s\n' $survivor_names | sort | tr '\n' ' ')"

echo "measured=$measured survivors=$survivors not_measured=$not_measured"
echo "expected survivors: $expected_sorted"
echo "actual survivors:   $actual_sorted"

if [ "$not_measured" -ne 0 ]; then
  echo "FAIL: $not_measured guard(s) could not be measured (pattern moved, or mutant did not build)"
  exit 1
fi
if [ "$expected_sorted" != "$actual_sorted" ]; then
  echo "FAIL: survivor set changed -- see the reasoning block in this script"
  exit 1
fi
echo "PASS: every verdict-bearing guard is killed by at least one test"
