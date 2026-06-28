# QF_LRA Farkas Evidence

## Problem Shape

Tiny unsat shape:

```text
x < 0
x > 0
```

Fragment: `QF_LRA`.

Expected result: `unsat`.

## Solver Route

The LRA route reasons over exact rationals/reals and produces a Farkas-style
linear certificate for an infeasible system. The arithmetic search that finds
the contradiction is not the trust anchor; the certificate is checked
independently.

## Evidence Artifact

Current checked artifact: `UnsatFarkas`.

The certificate contains rational multipliers whose linear combination cancels
variables and derives an impossible constant inequality.

## Checker

The focused evidence test is
`lra_unsat_evidence_carries_a_recheckable_farkas_certificate` in
[crates/axeyum-solver/tests/evidence.rs](../../../crates/axeyum-solver/tests/evidence.rs).

It checks:

- the evidence kind is `UnsatFarkas`;
- provenance records the Farkas backend;
- `Evidence::check` re-runs the independent Farkas verifier.

Tamper coverage is explicit:
`tampered_farkas_evidence_fails_its_own_check` zeroes a multiplier and verifies
that the independent checker rejects the proof.

## Lean Reconstruction

Status: checked for covered LRA shapes.

The broader Lean cross-check surface includes
`certified_lra_interpolant_both_farkas_certs_checked_by_real_lean` in
[crates/axeyum-solver/tests/lean_crosscheck.rs](../../../crates/axeyum-solver/tests/lean_crosscheck.rs).

## Trust Boundary

Trusted:

- not the simplex/Fourier-Motzkin search result by itself.

Checked:

- exact-rational certificate arithmetic;
- rejection of tampered multipliers;
- Lean reconstruction for covered generated modules.

Downgrade behavior:

- if the certificate fails to check, Axeyum must not report the unsat result as
  proved.

## Commands

Focused:

```sh
cargo test -p axeyum-solver --test evidence lra_unsat_evidence_carries_a_recheckable_farkas_certificate
cargo test -p axeyum-solver --test evidence tampered_farkas_evidence_fails_its_own_check
```

Lean cross-check:

```sh
cargo test -p axeyum-solver --test lean_crosscheck certified_lra_interpolant_both_farkas_certs_checked_by_real_lean
```

## Links

- [SMT Fragment Atlas](../../atlas/README.md)
- [atlas JSON](../../../artifacts/ontology/smt-fragments.json)
- [support matrix](../../research/08-planning/support-matrix.md)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [dominance scoreboard](../../../bench-results/DOMINANCE.md)
