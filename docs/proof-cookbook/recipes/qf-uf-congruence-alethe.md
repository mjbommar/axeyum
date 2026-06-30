# QF_UF Congruence And Alethe Evidence

## Problem Shape

Tiny unsat shape:

```text
f(a) = 0
a = b
not (f(b) = 0)
```

Fragment: `QF_UFBV` for the concrete regression, and the same congruence idea
applies to pure `QF_UF`.

Expected result: `unsat`.

## Solver Route

The search route finds a congruence conflict: from `a = b`, functional
consistency requires `f(a) = f(b)`. That contradicts the two asserted values.

The important point is that the functional-consistency step is not merely a
trusted Ackermann rewrite in this regression; it is derived in the proof route.

## Evidence Artifact

Current checked artifact: a zero-trust Alethe proof for the congruence conflict.

The proof uses congruence (`eq_congruent`) to derive the missing equality and
then closes the contradiction. The test asserts that the evidence carries no
trusted reduction steps for this query.

## Checker

The focused evidence test is
`qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate` in
[crates/axeyum-solver/tests/evidence.rs](../../../crates/axeyum-solver/tests/evidence.rs).

It checks:

- the evidence kind is `UnsatAletheProof`;
- `Evidence::check` re-runs the Alethe checker;
- the trust-step list is empty.

Pure declared-sort EUF coverage is tracked by
`qf_uf_declared_sort_equality_unsat_carries_zero_trust_alethe_certificate`.

## Lean Reconstruction

Status: checked for covered EUF shapes.

Relevant real-Lean cross-checks live in
[crates/axeyum-solver/tests/lean_crosscheck.rs](../../../crates/axeyum-solver/tests/lean_crosscheck.rs),
including `qf_uf_declared_sort_equality_checks_in_real_lean` and
`qf_ufbv_refutation_checks_in_real_lean`.

## Trust Boundary

Trusted:

- not the congruence step in the focused zero-trust regression; the proof
  derives it.

Checked:

- Alethe proof validation;
- the in-tree congruence explanation path;
- real-Lean reconstruction for covered shapes.

Downgrade behavior:

- if the route cannot build or check the proof, it must not upgrade the answer
  to a certified proof claim.

## Math Examples Using This Route

Use this route when the mathematical object is a finite function, quotient,
operation table, homomorphism, module, ideal, tensor map, or action law whose
bad row reduces to an equality or congruence conflict.

Canonical examples:

- [Equivalence Classes](../../../artifacts/examples/math/equivalence-classes-v0/)
  uses `quotient-map-congruence-conflict.smt2`.
- [Function Composition](../../../artifacts/examples/math/function-composition-v0/)
  uses a composition-application conflict over finite functions.
- [Finite Algebra Homomorphisms](../../../artifacts/examples/math/finite-algebra-homomorphisms-v0/)
  uses `homomorphism-preservation-congruence-conflict.smt2`.
- [Finite Groups](../../../artifacts/examples/math/finite-groups-v0/) and
  [Finite Monoids](../../../artifacts/examples/math/finite-monoids-v0/) use
  operation-congruence and associativity-table conflicts.
- [Finite Order Lattices](../../../artifacts/examples/math/finite-order-lattices-v0/),
  [Finite Permutation Groups](../../../artifacts/examples/math/finite-permutation-groups-v0/),
  [Finite Vector Spaces](../../../artifacts/examples/math/finite-vector-spaces-v0/),
  [Finite Dual Spaces](../../../artifacts/examples/math/finite-dual-spaces-v0/),
  [Finite Modules](../../../artifacts/examples/math/finite-modules-v0/),
  [Finite Ideals](../../../artifacts/examples/math/finite-ideals-v0/), and
  [Finite Tensor Products](../../../artifacts/examples/math/finite-tensor-products-v0/)
  provide the shared equality-heavy algebra family now grouped by
  `family_finite_algebra_alethe`.

The focused resource regression is
`cargo test -p axeyum-solver --test math_resource_uf_routes`.

## Commands

Focused:

```sh
cargo test -p axeyum-solver --test evidence qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate
cargo test -p axeyum-solver --test evidence qf_uf_declared_sort_equality_unsat_carries_zero_trust_alethe_certificate
```

Lean cross-checks:

```sh
cargo test -p axeyum-solver --test lean_crosscheck qf_uf_declared_sort_equality_checks_in_real_lean
cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_refutation_checks_in_real_lean
```

## Links

- [SMT Fragment Atlas](../../atlas/README.md)
- [atlas JSON](../../../artifacts/ontology/smt-fragments.json)
- [support matrix](../../research/08-planning/support-matrix.md)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [dominance scoreboard](../../../bench-results/DOMINANCE.md)
