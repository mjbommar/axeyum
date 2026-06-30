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

## Math Examples Using This Route

Use this route when the false mathematical claim reduces to exact rational
linear equalities or inequalities. The route is not floating-point analysis and
not a nonlinear theorem prover.

Canonical examples:

- [Linear Algebra Rational](../../../artifacts/examples/math/linear-algebra-rational-v0/)
  uses a singular inconsistent linear-system row.
- [Finite Probability](../../../artifacts/examples/math/finite-probability-v0/)
  uses bad normalization and Bayes-posterior rows over exact probability
  tables.
- [Finite Product Measure](../../../artifacts/examples/math/finite-product-measure-v0/)
  uses a bad product-probability row after exact replay computes the product
  mass.
- [Finite Random Variables](../../../artifacts/examples/math/finite-random-variables-v0/)
  uses a bad pushforward-distribution row after exact replay computes the
  outcome mass.
- [Finite Integration](../../../artifacts/examples/math/finite-integration-v0/)
  uses a bad expectation row after exact finite weighted-sum replay computes
  the integral.
- [Finite Calculus Shadows](../../../artifacts/examples/math/calculus-riemann-sum-v0/)
  uses a false polynomial-integral row after exact antiderivative replay
  computes the integral.
- [Calculus Algebraic Shadow](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
  uses a false derivative-value row after exact polynomial derivative replay
  computes the derivative at a point.
- [Complex Plane Transforms](../../../artifacts/examples/math/complex-plane-transforms-v0/)
  uses a bad unit-square real-part row after exact real-pair replay computes
  `i^2 = -1`.
- [Rational Multivariable Calculus](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
  uses a bad gradient-component row after exact bivariate polynomial derivative
  replay computes the gradient.
- [Sequence And Limit Shadows](../../../artifacts/examples/math/sequence-limit-shadow-v0/)
  uses a bounded Cauchy-tail row after exact finite replay computes the maximum
  pairwise distance.
- [Finite Martingales](../../../artifacts/examples/math/finite-martingales-v0/)
  uses a bad conditional-expectation row after exact finite filtration replay.
- [Finite Markov Chain](../../../artifacts/examples/math/finite-markov-chain-v0/)
  and [Finite Hitting Times](../../../artifacts/examples/math/finite-hitting-times-v0/)
  use malformed stochastic-row and expected-time equations.
- [Least Squares Regression](../../../artifacts/examples/math/least-squares-regression-v0/)
  uses a bad normal-equation coefficient row.
- [Real Analysis Rational](../../../artifacts/examples/math/real-analysis-rational-v0/)
  and [Metric Continuity](../../../artifacts/examples/math/metric-continuity-v0/)
  use bounded exact-rational epsilon-delta shadows, not general continuity
  theorems.
- [Rational Polynomial Factorization](../../../artifacts/examples/math/polynomial-factorization-rational-v0/)
  uses a fixed negative-discriminant row after exact polynomial replay computes
  the discriminant of `x^2 + 1`.
- [Numerical Linear Algebra](../../../artifacts/examples/math/numerical-linear-algebra-v0/),
  [Random Matrix Finite](../../../artifacts/examples/math/random-matrix-finite-v0/),
  [Spectral Linear Algebra](../../../artifacts/examples/math/spectral-linear-algebra-v0/),
  and [Matrix Invariants](../../../artifacts/examples/math/matrix-invariants-v0/)
  use bad residual, trace-moment, eigenpair, and characteristic-polynomial rows
  where the final contradiction is exact rational linear arithmetic.

The focused resource regression is
`cargo test -p axeyum-solver --test math_resource_lra_routes`.

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
- [Real Algebra RCF Shadow pack](../../../artifacts/examples/math/reals-rcf-shadow-v0/)
- [Calculus Algebraic Shadow pack](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
- [Complex Plane Transforms pack](../../../artifacts/examples/math/complex-plane-transforms-v0/)
- [Finite Calculus Shadows pack](../../../artifacts/examples/math/calculus-riemann-sum-v0/)
- [Rational Multivariable Calculus pack](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
- [Sequence And Limit Shadows pack](../../../artifacts/examples/math/sequence-limit-shadow-v0/)
- [Rational Polynomial Factorization pack](../../../artifacts/examples/math/polynomial-factorization-rational-v0/)
