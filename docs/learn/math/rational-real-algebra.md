# Rational And Real Algebra

Concept rows:

- `curriculum_rationals`, `curriculum_reals`, and `curriculum_polynomials` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_exact_vs_floating_arithmetic` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
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
- [finite-root-finding-v0](../../../artifacts/examples/math/finite-root-finding-v0/)
- [finite-separation-v0](../../../artifacts/examples/math/finite-separation-v0/)
- [finite-kkt-v0](../../../artifacts/examples/math/finite-kkt-v0/)
- [finite-active-set-qp-v0](../../../artifacts/examples/math/finite-active-set-qp-v0/)
- [finite-sdp-v0](../../../artifacts/examples/math/finite-sdp-v0/)
- [finite-gradient-descent-v0](../../../artifacts/examples/math/finite-gradient-descent-v0/)
- [finite-line-search-v0](../../../artifacts/examples/math/finite-line-search-v0/)
- [finite-wolfe-line-search-v0](../../../artifacts/examples/math/finite-wolfe-line-search-v0/)
- [finite-projected-gradient-v0](../../../artifacts/examples/math/finite-projected-gradient-v0/)
- [finite-proximal-gradient-v0](../../../artifacts/examples/math/finite-proximal-gradient-v0/)
- [matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/)
- [multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
- [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
- [convexity-rational-v0](../../../artifacts/examples/math/convexity-rational-v0/)
- [coordinate-geometry-v0](../../../artifacts/examples/math/coordinate-geometry-v0/)
- [incidence-geometry-v0](../../../artifacts/examples/math/incidence-geometry-v0/)
- [rigid-configuration-geometry-v0](../../../artifacts/examples/math/rigid-configuration-geometry-v0/)
- [affine-geometry-v0](../../../artifacts/examples/math/affine-geometry-v0/)
- [orientation-area-geometry-v0](../../../artifacts/examples/math/orientation-area-geometry-v0/)
- [finite-circle-geometry-v0](../../../artifacts/examples/math/finite-circle-geometry-v0/)
- [finite-inversion-geometry-v0](../../../artifacts/examples/math/finite-inversion-geometry-v0/)
- [finite-cyclic-geometry-v0](../../../artifacts/examples/math/finite-cyclic-geometry-v0/)

Companion map:

- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## What Axeyum Checks

The real-algebra path is currently exact rational arithmetic plus algebraic
shadows of real reasoning. It checks density witnesses, additive inverses,
fixed order facts, rational interval/ball inclusions, bounded epsilon-delta
samples, ordered-field real witnesses, small nonlinear polynomial constraints,
fixed-degree polynomial identities and roots, rational polynomial
factorization/division/GCD/square-free replay, finite generating-function
coefficient extraction and Cauchy-product replay, finite recurrence-prefix and
companion-matrix replay, finite bisection/Newton root-finding replay, finite
convex-hull/separating-hyperplane replay, finite KKT stationarity and
complementary-slackness replay, finite active-set QP replay, finite SDP
primal/dual slack replay, finite gradient-descent step replay, finite
line-search replay, finite Wolfe line-search replay, finite projected-gradient
replay, finite proximal-gradient replay, LP feasibility and
infeasibility certificates, finite convexity and monotonicity checks, exact
rational gradients, Jacobian chain-rule replay, Hessian minor checks,
midpoints, collinearity determinants, squared distances, affine maps, signed
areas, line-incidence equations, non-parallel line intersections, affine area
scaling, barycentric point-inside checks, point-on-circle rows, tangent-line
perpendicularity, chord-midpoint perpendicularity, unit-circle inversion images,
inverse-distance products, inversion collinearity, cyclic quadrilateral
membership, diagonal-intersection replay, and opposite-angle dot products. The
matrix-invariants pack adds a fixed characteristic polynomial, root evaluation,
Cayley-Hamilton replay, and exact eigenvalue interval checks.

This is where Axeyum can teach that many "real" examples have a small rational
core that is directly replayable.

The checked rows in this page use exact rational arithmetic unless they
explicitly say otherwise. A finite Newton step, residual bound, least-squares
normal equation, or rational epsilon-delta sample can be replayed exactly; that
does not certify floating-point rounding behavior, conditioning, numerical
stability, convergence rates, or a general real-analysis theorem. Those claims
stay in the numerical-honesty or Lean-horizon lane until a separate route
exists.

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

For finite root finding, keep the claim as one exact rational algorithm step:

```text
f(x) = x^2 - 2
[1,2] -> [1,3/2] by one bisection step
x_0 = 3/2 -> x_1 = 17/12 by one Newton step
```

The `finite-root-finding-v0` validator recomputes polynomial values, the
sign-changing bisection half, the derivative, the Newton iterate, and the
fixed residual decrease. Its bad row rejects the false claim `x_1 = 4/3`
after exact replay computes `x_1 = 17/12`, then checks the final contradiction
with QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Root Finding](finite-root-finding-end-to-end.md).

For finite separation, encode a rational triangle, convex weights, and a
separator:

```text
vertices = (0,0), (1,0), (0,1)
weights = 1/3, 1/3, 1/3
normal = (1,1)
threshold = 1
outside = (2,2)
```

The `finite-separation-v0` validator checks the convex-combination witness,
recomputes every separator dot product, checks the tight supporting face, and
rejects the false claim `normal . outside <= 1` after exact replay computes
`normal . outside = 4`. The bad row routes that final exact-linear conflict
through checked QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Hyperplane Separation](finite-separation-end-to-end.md).

For a finite KKT check, encode one constrained quadratic:

```text
minimize (x - 2)^2
subject to x <= 1
x = 1
lambda = 2
```

The `finite-kkt-v0` validator recomputes the feasible finite-grid objective
values, derivative, stationarity residual, and complementary-slackness product.
Its bad row changes the multiplier to `1`, computes stationarity residual
`-1`, and checks the resulting stationarity-error contradiction through
QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite KKT Checks](finite-kkt-end-to-end.md).

For a finite active-set QP check, encode a box-constrained quadratic:

```text
f(x,y) = (x - 2)^2 + (y - 1)^2
x <= 1
y >= 0
active face: x = 1
candidate = (1,1)
```

The `finite-active-set-qp-v0` validator recomputes the unconstrained minimizer,
the active-face candidate, active and inactive slacks, KKT stationarity, and
complementarity. Its bad row claims `(1,0)` solves the same active-face
subproblem; exact replay computes free-coordinate stationarity error `2`, and
the final nonpositive-error contradiction is checked through QF_LRA/Farkas
evidence. For a focused trace, read
[End To End: Finite Active-Set QP Checks](finite-active-set-qp-end-to-end.md).

For a finite SDP check, encode one trace-one primal matrix and dual slack:

```text
C = [[1,0],
     [0,2]]
X = [[1,0],
     [0,0]]
y = 1
S = [[0,0],
     [0,1]]
```

The `finite-sdp-v0` validator recomputes two-by-two principal minors, trace,
objective value, slack matrix, dual objective, and primal-dual gap. Its bad row
changes the objective to `0`, computes objective error `1`, and checks the
resulting exact-linear contradiction through QF_LRA/Farkas evidence. For a
focused trace, read
[End To End: Finite SDP Checks](finite-sdp-end-to-end.md).

For a finite gradient-descent check, encode a fixed quadratic step:

```text
f(x,y) = x^2 + 2y^2
start = (1,1)
alpha = 1/4
next = (1/2,0)
```

The `finite-gradient-descent-v0` validator recomputes the gradient, Hessian,
step update, objective values, exact decrease, and descent-bound slack. Its bad
row changes the decrease to `2`, computes decrease error `3/4`, and checks the
resulting exact-linear contradiction through QF_LRA/Farkas evidence. For a
focused trace, read
[End To End: Finite Gradient Descent Checks](finite-gradient-descent-end-to-end.md).

For a finite line-search check, encode one exact Armijo backtracking trace:

```text
f(x) = x^2
x0 = 1
direction = -2
c = 1/4
trial alpha = 1
accepted alpha = 1/2
```

The `finite-line-search-v0` validator recomputes the derivative, directional
derivative, trial candidate, Armijo right-hand side, rejected-step violation,
accepted-step candidate, and accepted-step slack. Its bad row claims the
rejected trial step satisfies Armijo even though exact replay computes
violation `1`; the final contradiction is checked through QF_LRA/Farkas
evidence. For a focused trace, read
[End To End: Finite Line Search Checks](finite-line-search-end-to-end.md).

For a finite Wolfe line-search check, encode one exact quadratic line-search
certificate:

```text
f(x) = x^2
x0 = 1
direction = -2
c1 = 1/4
c2 = 1/2
accepted alpha = 1/2
```

The `finite-wolfe-line-search-v0` validator recomputes the derivative,
directional derivative, exact minimizer candidate, Wolfe sufficient-decrease
slack, and Wolfe curvature slack. Its bad row claims the full step `alpha = 1`
satisfies curvature even though exact replay computes curvature violation `2`;
the final nonpositive-violation contradiction is checked through
QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Wolfe Line Search Checks](finite-wolfe-line-search-end-to-end.md).

For a finite projected-gradient check, encode one interval-constrained step:

```text
f(x) = (x - 2)^2
C = [0,1]
x0 = 0
alpha = 1/2
```

The `finite-projected-gradient-v0` validator recomputes the derivative,
unconstrained trial point `2`, interval projection to `1`, projected objective
value, and exact decrease. Its bad row claims `3/2` is a feasible projected
point for `[0,1]`; the final upper-bound contradiction is checked through
QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Projected Gradient Checks](finite-projected-gradient-end-to-end.md).

For a finite proximal-gradient check, encode one L1-regularized quadratic step:

```text
f(x) = 1/2 * (x - 3)^2
g(x) = |x|
x0 = 0
alpha = 1/2
```

The `finite-proximal-gradient-v0` validator recomputes the derivative,
ordinary trial point `3/2`, L1 soft-threshold point `1`, the zero
positive-branch optimality residual, and exact composite decrease. Its bad row
claims `1/4` satisfies the proximal optimality equation; replay computes
residual `-3/2`, and the final nonzero-residual contradiction is checked
through QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Proximal Gradient Checks](finite-proximal-gradient-end-to-end.md).

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

For a finite circle-geometry check, encode one rational circle point and its
tangent:

```text
C = (0,0)
P = (3/5,4/5)
r^2 = 1
tangent line = (3/5)x + (4/5)y - 1 = 0
```

The validator recomputes `|P-C|^2 = 1`, checks that `P` lies on the tangent
line, and checks that tangent direction `(-4/5,3/5)` has dot product `0` with
the radius vector. The bad row claims `(1,1)` lies on the unit circle; exact
replay computes squared radius `2`, while the source QF_LRA artifact asserts
the malformed value `1` and checks that final equality conflict with
`UnsatFarkas` evidence.

For a finite inversion-geometry check, encode one rational point outside the
unit circle:

```text
P = (2,1)
|P|^2 = 5
I(P) = (2/5,1/5)
```

The validator recomputes the scale factor `1/5`, the inverse image, the inverse
radius squared `1/5`, the product `5 * 1/5 = 1`, and the determinant proving
the center, point, and inverse point are collinear. The bad row claims inverse
x-coordinate `1/2`; exact replay computes `2/5`, and the source QF_LRA artifact
checks that final conflict with `UnsatFarkas` evidence.

For a finite cyclic-geometry check, encode one square on the unit circle:

```text
A = (1,0)
B = (0,1)
C = (-1,0)
D = (0,-1)
```

The validator recomputes that all four points have squared radius `1`, both
diagonals have midpoint `(0,0)`, the diagonal directions have dot product `0`,
and the opposite angle vector pairs at `B` and `D` have zero dot product. The
bad row claims the diagonal intersection has x-coordinate `1/2`; exact replay
computes `0`, and the source QF_LRA artifact checks that final conflict with
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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-root-finding-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_root_finding_bad_newton_step_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-separation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_separation_bad_separator_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-kkt-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_kkt_bad_stationarity_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-active-set-qp-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_active_set_qp_bad_free_gradient_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sdp-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_sdp_bad_objective_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gradient-descent-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gradient_descent_bad_decrease_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-line-search-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_line_search_bad_armijo_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-wolfe-line-search-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_wolfe_line_search_bad_curvature_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-projected-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_projected_gradient_bad_projection_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-proximal-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_proximal_gradient_bad_proximal_point_artifact_emits_checked_farkas
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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-circle-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_circle_geometry_bad_radius_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-inversion-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_x_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cyclic-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_diagonal_intersection_artifact_emits_checked_farkas
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
For exact finite convexity and KKT replay, read
[End To End: Rational Convexity](convexity-rational-end-to-end.md) and
[End To End: Finite KKT Checks](finite-kkt-end-to-end.md). For exact finite
active-set QP, gradient descent, line search, projected gradient, and proximal gradient, read
[End To End: Finite Active-Set QP Checks](finite-active-set-qp-end-to-end.md),
[End To End: Finite Gradient Descent Checks](finite-gradient-descent-end-to-end.md)
and [End To End: Finite Line Search Checks](finite-line-search-end-to-end.md),
and [End To End: Finite Wolfe Line Search Checks](finite-wolfe-line-search-end-to-end.md),
and [End To End: Finite Projected Gradient Checks](finite-projected-gradient-end-to-end.md),
and [End To End: Finite Proximal Gradient Checks](finite-proximal-gradient-end-to-end.md). For exact
finite coordinate, incidence, rigid-configuration, affine, and oriented geometry replay, read
[End To End: Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md)
[End To End: Incidence Geometry](incidence-geometry-end-to-end.md), and
[End To End: Rigid Configuration Geometry](rigid-configuration-geometry-end-to-end.md).
For finite circle point, tangent, and chord replay, read
[End To End: Finite Circle Geometry](finite-circle-geometry-end-to-end.md).
For finite inversion replay, read
[End To End: Finite Inversion Geometry](finite-inversion-geometry-end-to-end.md).
For finite cyclic quadrilateral replay, read
[End To End: Finite Cyclic Geometry](finite-cyclic-geometry-end-to-end.md).

## Horizon

Completeness, arbitrary limits, continuity, compactness, integration, general
KKT sufficiency, constraint qualifications, proximal-gradient convergence, and
Wolfe line-search convergence, and general real-analysis theorems
remain Lean-horizon. Nonlinear real arithmetic closed-form
generating-function extraction, asymptotics, and SOS/RCF certificates are
future proof-route work, not assumed coverage.
