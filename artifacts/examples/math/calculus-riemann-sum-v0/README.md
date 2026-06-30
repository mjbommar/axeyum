# Calculus Riemann Sum V0

This pack deepens the `calculus` curriculum node with exact finite Riemann-sum
and antiderivative replay. It complements `calculus-algebraic-shadow-v0`, which
focuses on derivative rules and polynomial tangent/critical-point checks.

The examples are:

- left, right, and trapezoid sums for `f(x) = x` on `[0, 1]`;
- midpoint-rule exactness for an affine function on `[0, 2]`;
- antiderivative endpoint replay for `f(x) = 2x`;
- lower and upper sums for the monotone polynomial `x^2`;
- checked rejection of a false exact integral claim through source-linked
  QF_LRA/Farkas evidence;
- a fundamental-theorem/general-integration Lean-horizon row.

## Concepts

- `curriculum_calculus`
- `curriculum_reals`
- `curriculum_rationals`
- `curriculum_sequences_and_limits`
- `curriculum_polynomials`
- `field_real_analysis`
- `field_numerical_analysis`
- `field_differential_equations_and_dynamical_systems`

## Trust Story

The validator recomputes every listed rational partition, sample point,
polynomial value, finite sum, and antiderivative endpoint difference exactly.
Counterexample rows are accepted only when the claimed integral differs from
the exact polynomial integral. The false-integral row also links the final
actual-vs-claimed equality conflict to
`smt2/false-integral-farkas-conflict.smt2`, which Axeyum checks with
`UnsatFarkas` evidence.

This is finite checked evidence for concrete polynomial tables. It is not a
proof of Riemann integrability, convergence of arbitrary Riemann sums, or the
fundamental theorem of calculus. Those stay under Lean horizon until
kernel-checked artifacts exist.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-riemann-sum-v0
```
