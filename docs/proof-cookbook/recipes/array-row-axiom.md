# Array Read-Over-Write Axiom Evidence

## Problem Shape

Tiny unsat shape:

```text
select(store(a, i, v), j) != ite(i = j, v, select(a, j))
```

Fragment: array read-over-write over BV-indexed, BV-valued arrays.

Expected result: `unsat`.

## Solver Route

This is the McCarthy read-over-write law. The current route recognizes the
array axiom instance and emits a direct checked array-axiom certificate rather
than trusting a broad array elimination and then proving only the reduced
formula.

## Evidence Artifact

Current checked artifact: `UnsatArrayAxiom` with
`ArrayAxiomKind::ReadOverWrite`.

The evidence records the matched axiom kind and rechecks the original assertion.
The focused test requires that these small array-axiom routes carry no reduction
trust holes.

## Checker

The focused evidence test is `produce_evidence_certifies_small_array_axiom_unsats`
in [crates/axeyum-solver/tests/evidence.rs](../../../crates/axeyum-solver/tests/evidence.rs).

It checks:

- the evidence kind is `UnsatArrayAxiom`;
- the axiom kind is `ReadOverWrite` for the McCarthy case;
- `Evidence::check` rechecks the certificate against the parsed assertions;
- `trusted_steps` is empty for these direct structural certificates.

## Lean Reconstruction

Status: partial.

The array-axiom certificate is checked in tree. Lean coverage for arrays is
growing but should be stated per shape, not as blanket QF_ABV coverage.

## Trust Boundary

Trusted:

- not the direct read-over-write axiom in this recipe; it is rechecked by the
  array-axiom certificate.

Still partial elsewhere:

- broader array elimination and extensionality proof coverage;
- non-BV array component sorts.

Checked:

- direct array-axiom certificate validation for this read-over-write
  contradiction.

Downgrade behavior:

- unsupported array shapes must remain explicit partial-trust routes or return
  `unknown`, rather than silently inheriting this recipe's zero-trust claim.

## Commands

Focused:

```sh
cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats
```

Broader:

```sh
cargo test -p axeyum-solver --test evidence
```

## Links

- [SMT Fragment Atlas](../../atlas/README.md)
- [atlas JSON](../../../artifacts/ontology/smt-fragments.json)
- [support matrix](../../research/08-planning/support-matrix.md)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [QF_ABV dominance row](../../../bench-results/DOMINANCE.md)
