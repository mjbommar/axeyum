# Notes: 380-nt-certificates

Detail moved out of [`../status/380-nt-certificates.md`](../status/380-nt-certificates.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
