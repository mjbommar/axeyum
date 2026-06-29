# QF_LIA Diophantine Evidence

## Problem Shape

Tiny integer-unsat shape:

```text
x + y = 0
x - y = 1
```

Over the integers this implies `2*x = 1`, which has no solution.

Fragment: equality-heavy `QF_LIA` and covered integer-prelude slices.

Expected result: `unsat`.

## Solver Route

The Diophantine route normalizes integer equalities into a linear system
`A*x = b`. A fraction-free elimination may derive a row
`sum_i c_i*x_i = d` where `gcd(c_i)` does not divide `d`, or a constant
contradiction `0 = d` with `d != 0`.

The route is used by Axeyum's integer evidence layer. Some math resource packs,
such as integer LIA, gcd/Bezout, bounded number theory, modular arithmetic,
exact statistical tests, finite simplicial homology, induction patterns, and
descriptive statistics, still use finite replay for many rows today; this
recipe is their graduation path when those examples are emitted as solver-form
LIA obligations.

## Evidence Artifact

Current checked artifact: `UnsatDiophantine`.

The certificate records:

- the normalized original integer equalities;
- one integer multiplier per equality;
- the combined row's sorted variable coefficients;
- the combined row's constant;
- the divisibility contradiction.

The artifact is self-checking: the checker recomputes the combination from the
original equalities and then checks the gcd condition.

## Checker

Implementation links:

- [crates/axeyum-solver/src/lia_gcd.rs](../../../crates/axeyum-solver/src/lia_gcd.rs)
- [crates/axeyum-solver/src/evidence.rs](../../../crates/axeyum-solver/src/evidence.rs)
- [crates/axeyum-solver/src/int_reconstruct.rs](../../../crates/axeyum-solver/src/int_reconstruct.rs)

The checker is `check_diophantine_certificate`. It rejects wrong multiplier
counts, malformed combined rows, tampered multipliers, tampered constants,
certificates checked against a different original system, and satisfiable
systems that produce no certificate.

Related integer-interval shapes use the `IntInequality` Lean reconstruction
path rather than this exact gcd certificate, but both belong to the same
integer-prelude evidence family.

## Lean Reconstruction

Status: covered for the supported Diophantine and integer-interval slices.

`reconstruct_diophantine_to_lean_module` re-derives a Lean module for covered
Diophantine shapes. The unified `prove_unsat_to_lean_module` route also covers
selected integer-interval contradictions through `IntInequality`.

## Trust Boundary

Trusted:

- not the elimination/search result by itself;
- not finite modular-table examples until they emit this solver-form evidence.

Checked:

- the integer certificate against the original equalities;
- the gcd non-divisibility contradiction;
- Lean reconstruction where the shape is covered.

Downgrade behavior:

- if the certificate cannot be produced or checked, the result stays
  replay-only, proof-gap, or `unknown` depending on the caller.

## Commands

Focused certificate tests:

```sh
cargo test -p axeyum-solver diophantine
cargo test -p axeyum-solver certificate_tamper_is_rejected
```

Integer Lean reconstruction slice:

```sh
cargo test -p axeyum-solver --test int_inequality_lean_reconstruct
```

Resource packs currently linked as graduation targets:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/integer-lia-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/gcd-bezout-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/exact-statistical-tests-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-patterns-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
```

## Links

- [SMT Fragment Atlas](../../atlas/README.md)
- [support matrix](../../research/08-planning/support-matrix.md)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [dominance scoreboard](../../../bench-results/DOMINANCE.md)
- [Integer LIA pack](../../../artifacts/examples/math/integer-lia-v0/)
- [GCD Bezout pack](../../../artifacts/examples/math/gcd-bezout-v0/)
- [Number Theory pack](../../../artifacts/examples/math/number-theory-v0/)
- [Modular Arithmetic pack](../../../artifacts/examples/math/modular-arithmetic-v0/)
- [Exact Statistical Tests pack](../../../artifacts/examples/math/exact-statistical-tests-v0/)
- [Finite Simplicial Homology pack](../../../artifacts/examples/math/finite-simplicial-homology-v0/)
- [Induction Patterns pack](../../../artifacts/examples/math/induction-patterns-v0/)
- [Descriptive Statistics pack](../../../artifacts/examples/math/descriptive-statistics-v0/)
