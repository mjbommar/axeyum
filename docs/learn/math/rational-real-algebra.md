# Rational And Real Algebra

Concept rows:

- `curriculum_rationals`, `curriculum_reals`, and `curriculum_polynomials` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis`, `field_optimization_and_convexity`, and
  `field_geometry` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [rationals-lra-v0](../../../artifacts/examples/math/rationals-lra-v0/)
- [real-analysis-rational-v0](../../../artifacts/examples/math/real-analysis-rational-v0/)
- [reals-rcf-shadow-v0](../../../artifacts/examples/math/reals-rcf-shadow-v0/)
- [polynomial-identities-v0](../../../artifacts/examples/math/polynomial-identities-v0/)
- [matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/)
- [multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
- [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
- [convexity-rational-v0](../../../artifacts/examples/math/convexity-rational-v0/)
- [coordinate-geometry-v0](../../../artifacts/examples/math/coordinate-geometry-v0/)

## What Axeyum Checks

The real-algebra path is currently exact rational arithmetic plus algebraic
shadows of real reasoning. It checks density witnesses, additive inverses,
fixed order facts, rational interval/ball inclusions, bounded epsilon-delta
samples, ordered-field real witnesses, small nonlinear polynomial constraints,
fixed-degree polynomial identities and roots, LP feasibility and infeasibility
certificates, finite convexity and monotonicity checks, exact rational
gradients, Jacobian chain-rule replay, Hessian minor checks, midpoints,
collinearity determinants, and squared distances. The matrix-invariants pack
adds a fixed characteristic polynomial, root evaluation, Cayley-Hamilton
replay, and exact eigenvalue interval checks.

This is where Axeyum can teach that many "real" examples have a small rational
core that is directly replayable.

## Encode / Check Walkthrough

For a rational order check, encode:

```text
a = 1/3
b = 2/3
midpoint = 1/2
```

The validator checks both the ordering and the exact arithmetic identity. For a
bounded real-analysis shadow, encode exact rational neighborhoods:

```text
inner interval = [1/4, 3/4]
outer ball = {x | |x - 1/2| < 1/3}
max endpoint distance = 1/4

f(x) = 2*x + 1
a = 0
epsilon = 1
delta = 1/2
domain sample = -1/4, 0, 1/4
```

The `real-analysis-rational-v0` validator checks that `1/4 < 1/3`, recomputes
the finite `delta`-ball from the listed samples, checks the linear output
distances, and rejects the false claim that `delta = 3/4` works using
`x = 2/3`.

For a small real-algebra shadow, encode a nonlinear witness or a one-variable
quadratic obstruction:

```text
x = 3/2
y = 4/3
x * y = 2

p(x) = x^2 + 1
discriminant = -4
```

The `reals-rcf-shadow-v0` validator replays the exact product witness, checks
that `x^2 < 0` is impossible by the fixed square-nonnegative shape, and checks
that a negative-discriminant quadratic has no real root. For a polynomial check
outside the real-specific pack, encode a coefficient list:

```text
p = [6, -5, 1]  means  6 - 5*x + x^2
root = 2
quotient = [-3, 1]
```

The checker evaluates `p(2)` exactly and verifies
`p = (x - 2)(x - 3)`. For a matrix-invariant check, encode a fixed matrix and
its characteristic polynomial:

```text
A = [[2, 1],
     [1, 2]]
chi_A(lambda) = 3 - 4*lambda + lambda^2
```

The checker recomputes trace, determinant, root values, and the fixed
Cayley-Hamilton matrix polynomial exactly.

For a multivariable real-algebra shadow, encode a fixed bivariate polynomial
and rational point:

```text
f(x,y) = x^2 + 2xy + 3y^2 + x
point = (1,2)
grad f(point) = (7,14)
H_f(point) = [[2,2],
              [2,6]]
```

The `multivariable-calculus-rational-v0` validator differentiates each
monomial, recomputes the gradient and Hessian exactly, checks a directional
derivative as a dot product, replays a Jacobian chain-rule matrix product, and
rejects the false gradient `(7,13)`.

For a coordinate-geometry check, encode two endpoints and the proposed midpoint:

```text
A = (0, 0)
B = (4, 2)
M = (2, 1)
```

The checker recomputes both midpoint coordinates. For optimization, encode
linear constraints and a candidate assignment; the checker evaluates each
constraint exactly.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-identities-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
```

For a fuller trace through exact fraction replay, read
[End To End: Rational Midpoint](rational-midpoint-end-to-end.md).

## Horizon

Completeness, arbitrary limits, continuity, compactness, integration, and
general real-analysis theorems remain Lean-horizon. Nonlinear real arithmetic
and SOS/RCF certificates are future proof-route work, not assumed coverage.
