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
- [polynomial-factorization-rational-v0](../../../artifacts/examples/math/polynomial-factorization-rational-v0/)
- [generating-functions-v0](../../../artifacts/examples/math/generating-functions-v0/)
- [finite-recurrence-prefix-v0](../../../artifacts/examples/math/finite-recurrence-prefix-v0/)
- [matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/)
- [multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
- [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
- [convexity-rational-v0](../../../artifacts/examples/math/convexity-rational-v0/)
- [coordinate-geometry-v0](../../../artifacts/examples/math/coordinate-geometry-v0/)
- [incidence-geometry-v0](../../../artifacts/examples/math/incidence-geometry-v0/)
- [rigid-configuration-geometry-v0](../../../artifacts/examples/math/rigid-configuration-geometry-v0/)
- [affine-geometry-v0](../../../artifacts/examples/math/affine-geometry-v0/)
- [orientation-area-geometry-v0](../../../artifacts/examples/math/orientation-area-geometry-v0/)

## What Axeyum Checks

The real-algebra path is currently exact rational arithmetic plus algebraic
shadows of real reasoning. It checks density witnesses, additive inverses,
fixed order facts, rational interval/ball inclusions, bounded epsilon-delta
samples, ordered-field real witnesses, small nonlinear polynomial constraints,
fixed-degree polynomial identities and roots, rational polynomial
factorization/division/GCD/square-free replay, finite generating-function
coefficient extraction and Cauchy-product replay, finite recurrence-prefix and
companion-matrix replay, LP feasibility and
infeasibility certificates, finite convexity and monotonicity checks, exact
rational gradients, Jacobian chain-rule replay, Hessian minor checks,
midpoints, collinearity determinants, squared distances, affine maps, signed
areas, line-incidence equations, non-parallel line intersections, affine area
scaling, and barycentric point-inside checks. The
matrix-invariants pack adds a fixed characteristic polynomial, root evaluation,
Cayley-Hamilton replay, and exact eigenvalue interval checks.

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
`x = 2/3`, with checked `UnsatFarkas` evidence for the final output bound.
The adjacent `metric-continuity-v0` pack now carries the same checked
QF_LRA/Farkas route for a finite metric-space bad-delta row.

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
that a negative-discriminant quadratic has no real root, with a QF_LRA/Farkas
artifact for the final nonnegative-discriminant contradiction. For a polynomial check
outside the real-specific pack, encode a coefficient list:

```text
p = [6, -5, 1]  means  6 - 5*x + x^2
root = 2
quotient = [-3, 1]
```

The checker evaluates `p(2)` exactly and verifies
`p = (x - 2)(x - 3)`. The factorization pack adds exact rational division and
GCD examples:

```text
x^4 - 1 = (x - 1)(x + 1)(x^2 + 1)
(x^4 - 1) / (x - 1) = x^3 + x^2 + x + 1
gcd(x^3 - x, x^2 - 1) = x^2 - 1
```

It also rejects rational linear factors for `x^2 + 1` by recomputing the
negative discriminant, then checks the final nonnegative-discriminant conflict
through QF_LRA/Farkas evidence. For a finite generating-function check, encode
coefficient lists and replay convolution:

```text
(1 + 2*x + x^2)(1 + x + x^2)
  = 1 + 3*x + 4*x^2 + 3*x^3 + x^4
```

The `generating-functions-v0` validator recomputes every coefficient exactly
and separately checks a bounded Fibonacci prefix identity for
`(1 - x - x^2)F(x) = x`; the bad finite Cauchy-product coefficient row now
also carries a checked QF_LIA/Diophantine certificate.

For a direct finite recurrence-prefix check, encode the prefix rather than the
general theorem:

```text
F = [0, 1, 1, 2, 3, 5, 8]
```

The `finite-recurrence-prefix-v0` validator recomputes every listed Fibonacci
step, checks an affine recurrence prefix, and checks a companion-matrix state
trace. Its bad row rejects `F_6 = 9` after replay computes `F_6 = 8`.

For a matrix-invariant check, encode a fixed matrix and its characteristic
polynomial:

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
rejects the false gradient `(7,13)`. The bad-gradient row also routes the final
component conflict `gradient_y = 14` versus `gradient_y = 13` through checked
QF_LRA/Farkas evidence.

For a coordinate-geometry check, encode two endpoints and the proposed midpoint:

```text
A = (0, 0)
B = (4, 2)
M = (2, 1)
```

The checker recomputes both midpoint coordinates. For optimization, encode
linear constraints and a candidate assignment; the checker evaluates each
constraint exactly. The coordinate-geometry pack now also rejects a bad
squared-distance claim: exact replay computes `25` for `(1,1)` to `(4,5)`,
while the source QF_LRA artifact checks the malformed claim `26` with
`UnsatFarkas` evidence.

For an incidence-geometry check, encode a line as exact rational coefficients:

```text
2x - y + 1 = 0
```

The incidence checker evaluates `a*x + b*y + c` at each listed point. The bad
row computes line value `3` for `(2,2)` but the malformed point-on-line claim
requires `0`; the source QF_LRA artifact checks that final conflict with
`UnsatFarkas` evidence.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes reals_rcf_shadow_negative_discriminant_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-identities-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-factorization-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes polynomial_factorization_irreducible_quadratic_discriminant_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/generating-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-recurrence-prefix-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_recurrence_prefix_bad_value_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes multivariable_calculus_bad_gradient_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes coordinate_geometry_bad_distance_squared_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/incidence-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes incidence_geometry_bad_point_on_line_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rigid-configuration-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes rigid_configuration_bad_distance_table_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/affine-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/orientation-area-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
```

For fuller traces through exact fraction replay, bounded rational
real-analysis evidence, real-algebra shadow checks, coefficient-level
polynomial replay, and a checked false-root Diophantine row, read
[End To End: Rational Midpoint](rational-midpoint-end-to-end.md),
[End To End: Bounded Rational Real Analysis](real-analysis-rational-end-to-end.md),
[End To End: Real Algebra RCF Shadow](reals-rcf-shadow-end-to-end.md), and
[End To End: Polynomial Identities](polynomial-identities-end-to-end.md). For
factorization, division, and GCD replay, read
[End To End: Rational Polynomial Factorization](polynomial-factorization-end-to-end.md).
For finite coefficient extraction and convolution replay, read
[End To End: Generating Functions](generating-functions-end-to-end.md). For
finite recurrence-prefix replay, read
[End To End: Finite Recurrence Prefixes](finite-recurrence-prefix-end-to-end.md).
For matrix characteristic-polynomial replay, read
[End To End: Matrix Invariants](matrix-invariants-end-to-end.md). For exact
finite eigenpair and spectral-decomposition replay, read
[End To End: Spectral Linear Algebra](spectral-linear-algebra-end-to-end.md).
For exact multivariable derivative replay, read
[End To End: Rational Multivariable Calculus](multivariable-calculus-end-to-end.md).
For exact LP feasibility and Farkas threshold evidence, read
[End To End: Linear Optimization](linear-optimization-end-to-end.md).
For exact finite convexity replay, read
[End To End: Rational Convexity](convexity-rational-end-to-end.md). For exact
finite coordinate, incidence, rigid-configuration, affine, and oriented geometry replay, read
[End To End: Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md)
[End To End: Incidence Geometry](incidence-geometry-end-to-end.md), and
[End To End: Rigid Configuration Geometry](rigid-configuration-geometry-end-to-end.md).

## Horizon

Completeness, arbitrary limits, continuity, compactness, integration, and
general real-analysis theorems remain Lean-horizon. Nonlinear real arithmetic
closed-form generating-function extraction, asymptotics, and SOS/RCF
certificates are future proof-route work, not assumed coverage.
