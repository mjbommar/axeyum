# 380 — number-theory certificates

<!-- plan-section: lane-status -->

**Lane:** `nt-certificates`
**Status:** landed — ADR-0745
**Date:** 2026-08-30

## What this lane was for

ADR-0716 measured that ADR-0603's **row 2** (the boundary refutation) is
provably empty for ℕ, ℤ and ℚ, so number-theoretic dominance has to come from
rows 1 + 3: a statement, an executable, and a re-derivable certificate. It then
measured the row-3 obligation as unmet.

## The gap, re-measured rather than inherited

Positive controls in the same command, GNU `grep` (not the interactive
`ugrep`):

| file | `verify_`/`check_` fns | plain `fn`s |
| --- | --- | --- |
| `crates/axeyum-cas/src/ntheory.rs` | **0** | 39 |
| `crates/axeyum-cas/src/ntheory_advanced.rs` | **0** | 29 |
| `crates/axeyum-cas/src/taylor.rs` (control) | 8 | — |
| `crates/axeyum-cas/src/mvt.rs` (control) | 9 | — |

Confirmed: 68 number-theoretic functions, zero verifiers, in a crate whose
analysis modules carry 8–9 apiece.

## What landed

`crates/axeyum-cas/src/ntheory_certify.rs` — four certificate types, four
independent checkers, self-checking producers. Modular arithmetic is the
module's own so a shared `mod_pow` defect cannot fool both sides; agreement
with `ntheory::mod_pow` is tested at 150 points including modulus `i128::MAX`.

- `PrattCertificate` / `check_primality_certificate` — recursive Lucas.
- `CompositeCertificate` / `check_composite_certificate` — a divisor. Kept a
  **separate type**; the two directions are never interchangeable.
- `FactorizationCertificate` / `check_factorization_certificate` — factor list
  + per-base Pratt + product identity + strict ascending order.
- `CrtCertificate` / `check_crt_certificate` — `Solution` with a **least**
  common multiple, or a named `Inconsistent` pair.

33 adversarial fixtures, 0 failures. Plus the 40 pre-existing `ntheory` tests:
73 passing under `--lib ntheory`.

## Trust anchor

**Nothing reconstructs through `Kernel::add_declaration`, deliberately**, and
the module doc labels itself `cas-internal` (ADR-0601). Over unary numerals a
reconstruction of `n = d · e` would be an `Eq.refl` on a numeral tower —
exactly the `refl`-shaped, substance-free reconstruction
`scripts/check-cas-substance.py` exists to catch.

## Guard-kill measurement

`scripts/tests/test-ntheory-certificate-guards.sh`:
`measured=23 survivors=3 not_measured=0`, exit 0.

Twenty verdict-bearing guards each killed (sixteen by one test, four by two).
Three survivors — G1, G5, G10 — **found by the sweep, not predicted**, each
provably unable to change a verdict, each documented at its site and pinned in
`EXPECTED_SURVIVORS` with a two-way assertion.

The sweep failed twice on real conditions before passing (two patterns matched
in two places, silently leaving guards `NOT MEASURED`; then a changed survivor
set), which is better evidence it can fail than a synthetic control. It also
corrected a comment I had written confidently and wrongly — the zero-exponent
fixture kills G9, not G5.

## Gating

- `scripts/check-ntheory-certificates.sh` — fixture suite with a **ratcheted
  nonzero** count (floor 33). Verified both ways: passes at 33, exits 1 at 999.
- Registered in **both** `scripts/check.sh` and the `justfile`;
  `check-aggregate-scope.sh` green at 64 recorded divergences, unchanged.
- The mutation sweep (~23 incremental builds) is deliberately **not** in the
  aggregate chain.

## What the row-1 + row-3 claim honestly becomes

Complete for **4** routines: primality (both directions), factorization, CRT
(both directions). Still **false** for the other 64 functions across the two
files — `legendre_symbol`, `jacobi_symbol`, `euler_phi`, `mod_inverse`,
`divisor_sigma` and the rest remain bare computation. Four routines, not a
subject.

## Next

- Legendre symbol via Euler's criterion at a certified prime; Jacobi symbol via
  a certified factorization. Both are natural now that `PrattCertificate`
  exists, and neither was claimed here.
- `euler_phi` from a `FactorizationCertificate` — the certificate already
  carries everything the formula needs.
