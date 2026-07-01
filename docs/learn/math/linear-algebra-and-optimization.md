# Linear Algebra And Optimization

Concept rows:

- `curriculum_linear_algebra`, `field_linear_algebra`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `field_functional_analysis_and_operator_theory` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [linear-algebra-rational-v0](../../../artifacts/examples/math/linear-algebra-rational-v0/)
- [finite-vector-spaces-v0](../../../artifacts/examples/math/finite-vector-spaces-v0/)
- [finite-dual-spaces-v0](../../../artifacts/examples/math/finite-dual-spaces-v0/)
- [inner-product-spaces-rational-v0](../../../artifacts/examples/math/inner-product-spaces-rational-v0/)
- [finite-modules-v0](../../../artifacts/examples/math/finite-modules-v0/)
- [finite-tensor-products-v0](../../../artifacts/examples/math/finite-tensor-products-v0/)
- [numerical-linear-algebra-v0](../../../artifacts/examples/math/numerical-linear-algebra-v0/)
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
- [spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/)
- [matrix-invariants-v0](../../../artifacts/examples/math/matrix-invariants-v0/)
- [random-matrix-finite-v0](../../../artifacts/examples/math/random-matrix-finite-v0/)
- [least-squares-regression-v0](../../../artifacts/examples/math/least-squares-regression-v0/)
- [finite-simplicial-homology-v0](../../../artifacts/examples/math/finite-simplicial-homology-v0/)
- [finite-universal-coefficient-shadow-v0](../../../artifacts/examples/math/finite-universal-coefficient-shadow-v0/)
- [multivariable-calculus-rational-v0](../../../artifacts/examples/math/multivariable-calculus-rational-v0/)
- [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
- [convexity-rational-v0](../../../artifacts/examples/math/convexity-rational-v0/)
- [incidence-geometry-v0](../../../artifacts/examples/math/incidence-geometry-v0/)
- [rigid-configuration-geometry-v0](../../../artifacts/examples/math/rigid-configuration-geometry-v0/)
- [affine-geometry-v0](../../../artifacts/examples/math/affine-geometry-v0/)
- [orientation-area-geometry-v0](../../../artifacts/examples/math/orientation-area-geometry-v0/)
- [finite-circle-geometry-v0](../../../artifacts/examples/math/finite-circle-geometry-v0/)
- [finite-inversion-geometry-v0](../../../artifacts/examples/math/finite-inversion-geometry-v0/)
- [finite-cyclic-geometry-v0](../../../artifacts/examples/math/finite-cyclic-geometry-v0/)
- [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)
- [finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/)

Companion index:

- [Matrix Computation Index](matrix-computation-index.md)
- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## What Axeyum Checks

The linear path uses exact rational matrices. It replays `A*x = b`, checks
`L*U = A`, rejects a malformed LU product entry through checked
QF_LRA/Farkas evidence, validates a row-scaling inconsistency certificate,
checks LP feasibility witnesses, checks a tiny Farkas infeasibility
certificate, and replays finite convexity/threshold and finite-dimensional
norm/operator examples. The least-squares regression slice checks normal equations,
residual orthogonality, RSS comparison, and a checked `UnsatFarkas`
bad-coefficients certificate. The finite-vector-space slice adds `F2^2`,
subspace/span replay,
linear-map kernel/image replay, rank-nullity by finite cardinality, and
checked QF_UF/Alethe non-subspace rejection. The finite-dual-space slice adds covectors as
finite function tables, pointwise dual operations, dual-basis pairings,
annihilator recomputation, transpose-map replay, and checked QF_UF/Alethe
bad-covector rejection. The exact rational inner-product slice adds symmetric
positive-definite Gram matrices, Cauchy-Schwarz replay for fixed vectors,
orthogonal projection replay, Gram-Schmidt orthogonalization replay, and
QF_LRA/Farkas rejection of an indefinite bilinear form. The finite-module
slice adds ring actions on finite additive groups,
generated submodules, module homomorphisms, kernel/image replay, quotient-module
tables, and checked QF_UF/Alethe non-submodule rejection. The finite-tensor-product
slice adds bilinear maps, finite universal-factorization shadows, Kronecker
products, and checked QF_UF/Alethe bad-bilinear-map rejection over `F2`. The
numerical-linear-algebra slice adds exact residual bounds, rational interval
boxes for solutions, and a one-step Jacobi contraction check, with a checked
QF_LRA/Farkas bad-bound certificate. The finite-recurrence-prefix slice adds
Fibonacci and affine recurrence replay plus a companion-matrix state trace,
with a checked QF_LRA/Farkas bad finite value certificate. The
finite-root-finding slice adds exact bisection/Newton iteration replay,
residual-decrease checking, and a checked QF_LRA/Farkas bad Newton-step
certificate. The finite-separation slice adds exact convex-hull membership,
separating-hyperplane score replay, supporting-face checking, and a checked
QF_LRA/Farkas bad-separator certificate. The finite-KKT slice adds exact
constrained-quadratic grid replay, stationarity replay, complementary-slackness
checking, and a checked QF_LRA/Farkas bad-stationarity certificate. The finite
active-set QP slice adds exact active-face replay, inactive-constraint slack
checking, and a checked QF_LRA/Farkas bad-free-gradient certificate. The finite
SDP slice adds two-by-two PSD replay, trace/objective arithmetic, dual-slack
matrix replay, zero duality-gap checking, and a checked QF_LRA/Farkas
bad-objective certificate. The finite-gradient-descent slice adds exact
quadratic gradient replay, step-update replay, objective-decrease checking,
finite descent-bound replay, and a checked QF_LRA/Farkas bad-decrease
certificate. The finite line-search slice adds exact Armijo trial rejection,
one accepted backtracked step, and a checked QF_LRA/Farkas bad-acceptance
certificate. The finite Wolfe line-search slice adds exact Wolfe
sufficient-decrease and curvature replay plus a checked bad-curvature
certificate. The finite projected-gradient slice adds exact interval
projection after a trial step and a checked QF_LRA/Farkas bad-projection
certificate. The finite proximal-gradient slice adds exact L1 soft-threshold
replay after a trial step and a checked QF_LRA/Farkas bad-proximal-point
certificate. The finite random-matrix slice adds exact
matrix-valued probability tables, trace/determinant moments, expected Gram
matrices, rank distributions, and checked QF_LRA/Farkas bad trace-square and
bad expected-rank certificates. The spectral slice checks exact finite
eigenpair replay, orthogonal eigenbasis arithmetic, Rayleigh quotients, and
`P*D*P^-1` reconstruction for a fixed rational matrix, plus a QF_LRA/Farkas
bad-Rayleigh-quotient certificate and a bad-eigenpair certificate. The matrix-invariants
slice checks trace, determinant, characteristic roots, Cayley-Hamilton replay,
finite Gershgorin intervals, and QF_LRA/Farkas bad-trace plus
bad-polynomial certificates for a fixed rational matrix. The
multivariable-calculus slice checks Jacobian and Hessian matrices generated by
fixed bivariate polynomial maps, including a chain-rule matrix product and a
positive-definite Hessian certificate by leading principal minors. The finite
homology slice builds boundary matrices for a fixed simplicial complex,
computes exact ranks, replays Betti numbers over `Q`, and checks a
QF_LIA/Diophantine bad boundary coefficient certificate. The finite
universal-coefficient shadow slice dualizes a one-entry integer boundary
matrix, replays `H^1 = Z/2`, checks the fixed degree-one Hom/Ext row, and
rejects a bad `H^1 = 0` identity with QF_UF/Alethe evidence. The finite
convexity slice checks midpoint Jensen replay, finite-grid second differences,
affine threshold monotonicity, and bad midpoint-convexity rejection over exact
rational data. The finite
Chebyshev-system slice checks Vandermonde unisolvence, interpolation replay,
alternating residual signs, duplicate-node rejection, and a checked bad
interpolation sample plus a checked bad alternation-magnitude claim over exact
rational sample grids. The finite-operator slice also checks a bad
Chebyshev-prefix value after exact recurrence replay computes `T3(1/2) = -1`.
The incidence-geometry slice checks line equations and
non-parallel line intersections as tiny exact linear systems, then rejects bad
intersection-coordinate and point-on-line rows through QF_LRA/Farkas evidence.
The
rigid-configuration slice treats pairwise squared-distance tables as finite
matrix-like data, checks translation and congruent-triangle witnesses, and
rejects bad translation-image and distance-table rows through QF_LRA/Farkas
evidence.
The finite circle-geometry slice checks point-on-circle equations,
tangent-line/radius perpendicularity, chord-midpoint perpendicularity, and
circle-line intersections as small exact vector calculations, then rejects bad
radius and bad line-intersection rows through QF_LRA/Farkas evidence.
The finite inversion-geometry slice checks unit-circle inversion as scalar
vector replay, inverse-distance products, and collinearity determinants, then
rejects bad inverse-coordinate and inverse-distance-product rows through
QF_LRA/Farkas evidence.
The finite cyclic-geometry slice checks an inscribed square as exact vector
data: radius-squared rows, diagonal midpoints, diagonal dot products, and
opposite-angle dot products, then rejects bad diagonal-intersection and
opposite-angle rows through QF_LRA/Farkas evidence.

This is a strong resource path because the trusted checker can be small: matrix
multiplication, vector norms, linear inequalities, and certificate arithmetic.

## Encode / Check Walkthrough

For a linear system, encode the matrix, candidate vector, and right-hand side:

```text
A = [[2, 1],
     [1,-1]]
x = [1, 2]
b = [4,-1]
```

The validator recomputes `A*x` and checks it equals `b`. For an LU witness, it
recomputes `L*U = A` and checks triangular shape. For optimization, it evaluates
each linear inequality at the candidate point and checks Farkas multipliers when
the pack claims infeasibility.

For finite-field linear algebra, encode `F2^2` as four vectors:

```text
vectors = 00, 10, 01, 11
span(10) = {00, 10}
kernel(projection_to_first_coordinate) = {00, 01}
image(projection_to_first_coordinate) = {00, 10}
```

The `finite-vector-spaces-v0` validator checks vector-space laws by
enumeration, recomputes spans, verifies linear-map preservation, and checks
rank-nullity as `dim(domain) = dim(kernel) + dim(image)`. Its bad subspace row
links the missing-sum closure failure to checked QF_UF/Alethe evidence.

For dual spaces, keep the same carrier and encode each covector by evaluation:

```text
x(00)=0, x(10)=1, x(01)=0, x(11)=1
y(00)=0, y(10)=0, y(01)=1, y(11)=1
dual_basis = x, y
annihilator({00,10}) = {zero,y}
```

The `finite-dual-spaces-v0` validator checks that `x`, `y`, and `x+y` are
linear functionals, dual addition is pointwise, the listed dual basis pairs
with `10,01` as the identity matrix, annihilators are recomputed from the
evaluation table, and transpose maps satisfy `(T* phi)(v) = phi(Tv)`. The bad
covector row links the failed additivity equation to checked QF_UF/Alethe
evidence.

For rational inner-product examples, encode the Gram matrix and the vectors:

```text
G = [[1, 0],
     [0, 1]]
u = (1, 2)
v = (3,-1)
<u,v> = 1
<u,u> = 5
<v,v> = 10
```

The `inner-product-spaces-rational-v0` validator checks symmetry and positive
principal minors for a weighted Gram matrix, recomputes the listed dot products,
checks the fixed Cauchy-Schwarz inequality `1^2 <= 5*10`, and verifies a
projection onto the span of `(1,1)`:

```text
proj_(1,1)(2,3) = (5/2, 5/2)
residual = (-1/2, 1/2)
<residual, (1,1)> = 0
```

It also replays the second Gram-Schmidt vector as `(1/2,-1/2)` and rejects a
diagonal form with negative norm square. The checked projection-orthogonality
bad row reuses the same residual and rejects the malformed claim
`<residual,(1,1)> = 1` after replay computes `0`.

For module-flavored linear algebra, encode `Z/4Z` as a module over itself:

```text
submodule generated by 2 = {0, 2}
times_two(1) = 2
times_two(2) = 0
quotient cosets = E={0, 2}, O={1, 3}
```

The `finite-modules-v0` validator checks the finite module laws, recomputes
the generated submodule, checks the multiplication-by-`2` homomorphism,
recomputes kernel and image, and verifies quotient-module addition and scalar
action from representatives. Its bad submodule row links the failed
scalar-closure equation to checked QF_UF/Alethe evidence.

For tensor-product flavored linear algebra, encode the finite bilinear table:

```text
beta(v,0) = 00
beta(10,1) = 10
beta(01,1) = 01
beta(11,1) = 11
```

The `finite-tensor-products-v0` validator checks bilinearity in both
arguments, verifies the listed tensor basis spans `F2^2 tensor F2`, checks a
linear projection factorization, recomputes a fixed Kronecker product, and
links a failed left-additivity row to checked QF_UF/Alethe evidence.

For convexity, the validator checks exact finite inequalities:

```text
f(x) = x^2
a = -1
b = 3
m = 1
f(m) = 1 <= (f(a) + f(b)) / 2 = 5

grid values for x^2 on -2,-1,0,1,2 = 4,1,0,1,4
second differences = 2,2,2
```

The convexity validator also rejects a false midpoint-convexity claim with
`f(-1)=0`, `f(0)=1`, and `f(1)=0`. For the numerical pack, it recomputes
`A*x_hat - b`, infinity norms, interval membership, and the first Jacobi update
using exact rational arithmetic. For random matrices, it checks finite atom
probabilities and recomputes weighted matrix statistics exactly. For spectral
linear algebra, it recomputes `A*v`, `lambda*v`, dot products, `v^T*A*v /
v^T*v`, and `P*D*P^-1` exactly, and rejects a false Rayleigh quotient after
replay computes `3`. For matrix invariants, it recomputes the
characteristic polynomial, evaluates listed roots, checks `A^2 - trace(A)*A +
det(A)*I = 0`, and validates finite eigenvalue intervals.

For an operator example, the finite-operator pack checks:

```text
||u+v||_1 <= ||u||_1 + ||v||_1
||A*x||_infty <= ||A||_row-sum * ||x||_infty
```

using exact rational arithmetic. Its bad norm row rejects
`||u+v||_1 <= 4` after replay computes `||u+v||_1 = 5`; its bad-bound row also
rejects the malformed claim `||A*x||_infty <= 2` after replay computes
`||A*x||_infty = 3`, with both final inequality conflicts checked by
QF_LRA/Farkas evidence.

For a finite root-finding example, the validator keeps the numerical method as
an exact finite trace:

```text
f(x) = x^2 - 2
[1,2] -> [1,3/2]
3/2 -> 17/12 by Newton's rule
```

It recomputes the polynomial values, derivative, iterate, and residual
decrease. The bad row rejects `17/12 = 4/3` through checked QF_LRA/Farkas
evidence, making it useful for numerical-analysis lessons without claiming a
general convergence theorem.

For a finite separation example, encode a convex hull and a separating normal:

```text
vertices = (0,0), (1,0), (0,1)
point = (1/3,1/3)
normal = (1,1)
threshold = 1
outside = (2,2)
```

The validator checks nonnegative convex weights summing to one, recomputes all
dot products, checks the tight face `{(1,0),(0,1)}`, and rejects a malformed
outside-point inequality through checked QF_LRA/Farkas evidence. This is the
finite-dimensional, exact-rational version of a separation certificate, not the
general theorem.

For a finite KKT example, encode one constrained quadratic and multiplier:

```text
minimize (x - 2)^2
subject to x <= 1
x = 1
lambda = 2
```

The `finite-kkt-v0` validator recomputes objective values on a finite feasible
grid, differentiates the quadratic, checks stationarity
`f'(1) + lambda = 0`, and checks complementary slackness. Its bad row changes
the multiplier to `1`, giving stationarity residual `-1` and stationarity error
`1`; the final contradiction `error = 1` versus `error = 0` is checked through
QF_LRA/Farkas evidence.

For a finite active-set QP example, encode one two-variable quadratic and a
working set:

```text
minimize (x - 2)^2 + (y - 1)^2
subject to x <= 1
           y >= 0
active face: x = 1
candidate = (1,1)
```

The `finite-active-set-qp-v0` validator recomputes the unconstrained minimizer
`(2,1)`, its violation of `x <= 1`, the active-face candidate `(1,1)`,
inactive slack for `y >= 0`, KKT stationarity with multiplier `2`, and the
zero complementarity products. Its bad row claims `(1,0)` solves the same
active-face subproblem; exact replay computes free stationarity error `2`, and
the final nonpositive-error contradiction is checked through QF_LRA/Farkas
evidence. For a focused trace, read
[End To End: Finite Active-Set QP Checks](finite-active-set-qp-end-to-end.md).

For a finite circle-geometry example, encode a point, tangent direction, and
circle-line chord as exact rational vectors:

```text
P = (3/5,4/5)
radius = (3/5,4/5)
tangent_direction = (-4/5,3/5)
A = (3,4), B = (3,-4), midpoint = (3,0)
line y = 0, endpoints = (-1,0),(1,0)
```

The `finite-circle-geometry-v0` validator recomputes the unit-circle equation,
the tangent-line value, the tangent/radius dot product, chord endpoint radii,
midpoints, the radius/chord dot product, and the horizontal line intersections.
Its checked bad rows reject `(1,1)` as a unit-circle point and reject a false
right-intersection x-coordinate `2`; exact replay computes squared radius `2`
and right-intersection x-coordinate `1`, and both final conflicts are checked
through QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Circle Geometry](finite-circle-geometry-end-to-end.md).

For a finite inversion-geometry example, encode the point and inverse image as
exact rational vectors:

```text
P = (2,1)
scale = 1 / |P|^2 = 1/5
I(P) = (2/5,1/5)
```

The `finite-inversion-geometry-v0` validator recomputes the scale, inverse
image, distance product, point/inverse dot product, and determinant for
collinearity with the center. Its bad row claims inverse x-coordinate `1/2`;
exact replay computes `2/5`, and the final conflict is checked through
QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Inversion Geometry](finite-inversion-geometry-end-to-end.md).

For a finite cyclic-geometry example, encode a square on the unit circle and a
`4 x 3` cyclic rectangle:

```text
A = (1,0)
B = (0,1)
C = (-1,0)
D = (0,-1)
rectangle sides = 4,3,4,3
rectangle diagonals = 5,5
```

The `finite-cyclic-geometry-v0` validator recomputes all four radii, both
diagonal midpoints, both diagonal directions, and opposite-angle vector pairs.
It also checks the rectangle's Ptolemy arithmetic `5*5 = 4*4 + 3*3`. Its bad
rows claim diagonal-intersection x-coordinate `1/2`, angle dot product `1`, and
Ptolemy right-hand side `24`; exact replay computes `0`, `0`, and `25`
respectively. The final conflicts are checked through QF_LRA/Farkas evidence.
For a focused trace, read
[End To End: Finite Cyclic Geometry](finite-cyclic-geometry-end-to-end.md).

For a finite SDP example, encode a two-by-two trace-one PSD matrix and dual
slack:

```text
C = [[1,0],
     [0,2]]
X = [[1,0],
     [0,0]]
y = 1
S = C - yI
```

The `finite-sdp-v0` validator checks the primal matrix and slack matrix by
two-by-two principal minors, recomputes `<I,X> = 1`, `<C,X> = 1`, and verifies
zero primal-dual gap. Its bad row changes the objective to `0`, giving
objective error `1`; the final contradiction `error = 1` versus `error = 0` is
checked through QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite SDP Checks](finite-sdp-end-to-end.md).

For a finite gradient-descent example, encode a quadratic, start point, step
size, and gradient:

```text
f(x,y) = x^2 + 2y^2
start = (1,1)
gradient = (2,4)
alpha = 1/4
next = (1/2,0)
```

The `finite-gradient-descent-v0` validator recomputes the gradient, Hessian,
next point, objective values `3` and `1/4`, decrease `11/4`, and finite
descent-bound slack `1/4`. Its bad row changes the decrease to `2`, giving
decrease error `3/4`; the final contradiction `error = 3/4` versus `error = 0`
is checked through QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Gradient Descent Checks](finite-gradient-descent-end-to-end.md).

For a finite line-search example, encode a one-dimensional quadratic and one
Armijo backtracking trace:

```text
f(x) = x^2
x0 = 1
direction = -2
c = 1/4
trial alpha = 1
accepted alpha = 1/2
```

The `finite-line-search-v0` validator recomputes the derivative, directional
derivative, rejected candidate, accepted candidate, Armijo right-hand sides,
positive rejection violation, and accepted-step slack. Its bad row claims the
rejected trial step satisfies Armijo; exact replay computes violation `1`, and
the final nonpositive-violation contradiction is checked through
QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Line Search Checks](finite-line-search-end-to-end.md).

For a finite Wolfe line-search example, encode a one-dimensional quadratic and
one exact Wolfe step:

```text
f(x) = x^2
x0 = 1
direction = -2
c1 = 1/4
c2 = 1/2
accepted alpha = 1/2
```

The `finite-wolfe-line-search-v0` validator recomputes the derivative,
directional derivative, exact minimizer, Wolfe sufficient-decrease slack,
Wolfe curvature slack, and the bad-row curvature violation for the full step
`alpha = 1`. The final nonpositive-violation contradiction is checked through
QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Wolfe Line Search Checks](finite-wolfe-line-search-end-to-end.md).

For a finite projected-gradient example, encode a one-dimensional quadratic and
an interval constraint:

```text
f(x) = (x - 2)^2
C = [0,1]
x0 = 0
alpha = 1/2
```

The `finite-projected-gradient-v0` validator recomputes the derivative,
unconstrained trial point `2`, projection to the interval endpoint `1`,
objective decrease from `4` to `1`, and the projection distance. Its bad row
claims `3/2` is feasible for `[0,1]`; the final upper-bound contradiction is
checked through QF_LRA/Farkas evidence. For a focused trace, read
[End To End: Finite Projected Gradient Checks](finite-projected-gradient-end-to-end.md).

For a finite proximal-gradient example, encode one L1-regularized quadratic:

```text
f(x) = 1/2 * (x - 3)^2
g(x) = |x|
x0 = 0
alpha = 1/2
lambda = 1
```

The `finite-proximal-gradient-v0` validator recomputes the derivative,
ordinary trial point `3/2`, L1 soft-threshold value `1`, zero positive-branch
optimality residual, composite objective decrease from `9/2` to `3`, and the
bad-row residual for a claimed prox point `1/4`. The final nonzero-residual
contradiction is checked through QF_LRA/Farkas evidence. For a focused trace,
read
[End To End: Finite Proximal Gradient Checks](finite-proximal-gradient-end-to-end.md).

For a Jacobian/Hessian bridge into optimization, encode:

```text
f(x,y) = x^2 + 2xy + 3y^2 + x
grad f(1,2) = (7,14)
H_f = [[2,2],
       [2,6]]
det(H_f) = 8
```

The `multivariable-calculus-rational-v0` validator recomputes the derivative
matrix entries and checks the positive principal minors exactly. Its
bad-gradient row also checks the final exact-linear contradiction
`gradient_y = 14` versus `gradient_y = 13` through QF_LRA/Farkas evidence.

For a finite Chebyshev-system example, the validator checks the quadratic
Vandermonde matrix on sample points `-1, 0, 1`:

```text
[[1, -1, 1],
 [1,  0, 0],
 [1,  1, 1]]
```

It recomputes determinant `2`, checks interpolation values for
`2 - x + 3*x^2`, rejects a duplicate-node grid whose determinant is `0`, and
rejects the false interpolation sample claim `p(1)=5` after replay computes
`p(1)=4`. It also checks the residual table `1/2, -1/2, 1/2` and rejects a
malformed uniform-error claim `2/3` after replay computes `1/2`. The bad-grid,
bad-sample, and bad-alternation rows route their final exact-linear conflicts
through checked QF_LRA/Farkas evidence.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/inner-product-spaces-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes inner_product_bad_projection_orthogonality_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
cargo test -p axeyum-solver --test math_resource_lra_routes spectral_bad_rayleigh_quotient_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-universal-coefficient-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes multivariable_calculus_bad_gradient_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_rejects_tampered_farkas_certificate
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/incidence-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes incidence_geometry_bad_point_on_line_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rigid-configuration-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes rigid_configuration_bad_translation_image_x_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes rigid_configuration_bad_distance_table_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/affine-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/orientation-area-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-circle-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_circle_geometry_bad_radius_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_circle_geometry_bad_line_intersection_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-inversion-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_x_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_distance_product_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cyclic-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_diagonal_intersection_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_opposite_angle_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_ptolemy_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_operator_bound_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
```

For fuller traces through exact matrix replay, a checked LP certificate,
finite rational convexity replay, matrix-invariant replay, multivariable
derivative/Jacobian replay, exact rational inner-product replay,
finite-field vector-space replay, finite dual-space replay, and finite module
replay, read
[Matrix Computation Index](matrix-computation-index.md),
[Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md),
[End To End: Linear System And LP Replay](linear-system-end-to-end.md),
[End To End: Linear Optimization](linear-optimization-end-to-end.md),
[End To End: Farkas Certificate Anatomy](farkas-certificate-anatomy-end-to-end.md),
[End To End: Rational Convexity](convexity-rational-end-to-end.md),
[End To End: Matrix Invariants](matrix-invariants-end-to-end.md),
[End To End: Spectral Linear Algebra](spectral-linear-algebra-end-to-end.md),
[End To End: Finite Random Matrices](random-matrix-finite-end-to-end.md),
[Random Matrix Moment Index](random-matrix-moment-index.md),
[End To End: Numerical Linear Algebra](numerical-linear-algebra-end-to-end.md),
[End To End: Finite Recurrence Prefixes](finite-recurrence-prefix-end-to-end.md),
[End To End: Finite Root Finding](finite-root-finding-end-to-end.md),
[End To End: Finite Hyperplane Separation](finite-separation-end-to-end.md),
[End To End: Finite KKT Checks](finite-kkt-end-to-end.md),
[End To End: Finite Active-Set QP Checks](finite-active-set-qp-end-to-end.md),
[End To End: Finite Line Search Checks](finite-line-search-end-to-end.md),
[End To End: Finite Wolfe Line Search Checks](finite-wolfe-line-search-end-to-end.md),
[End To End: Finite Projected Gradient Checks](finite-projected-gradient-end-to-end.md),
[End To End: Finite Proximal Gradient Checks](finite-proximal-gradient-end-to-end.md),
[End To End: Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md),
[End To End: Finite Universal Coefficient Shadow](finite-universal-coefficient-shadow-end-to-end.md),
[End To End: Descriptive Statistics And Regression](descriptive-statistics-regression-end-to-end.md),
[End To End: Rational Multivariable Calculus](multivariable-calculus-end-to-end.md),
[End To End: Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md),
[End To End: Incidence Geometry](incidence-geometry-end-to-end.md),
[End To End: Rigid Configuration Geometry](rigid-configuration-geometry-end-to-end.md),
[End To End: Finite Circle Geometry](finite-circle-geometry-end-to-end.md),
[End To End: Finite Inversion Geometry](finite-inversion-geometry-end-to-end.md),
[End To End: Finite Cyclic Geometry](finite-cyclic-geometry-end-to-end.md),
[End To End: Rational Inner Product Spaces](inner-product-spaces-end-to-end.md),
[End To End: Finite Vector Spaces](finite-vector-spaces-end-to-end.md),
[End To End: Finite Dual Spaces](finite-dual-spaces-end-to-end.md), and
[End To End: Finite Modules](finite-modules-end-to-end.md). For finite
multilinear replay, read
[End To End: Finite Tensor Products](finite-tensor-products-end-to-end.md). For
finite Chebyshev-system interpolation and alternation replay, read
[End To End: Finite Chebyshev Systems](finite-chebyshev-systems-end-to-end.md).

## Proof Upgrade Notes

Exact rational matrix witnesses, projections, residuals, spectra, random-matrix
moments, and satisfiable finite-dimensional operator rows start as
[Finite Model Replay](../../proof-cookbook/recipes/finite-model-replay.md).
Infeasible rational systems, LP thresholds, bad residual bounds, malformed
eigenpairs, bad Rayleigh-quotient rows, bad characteristic-polynomial rows,
bad operator-bound and bad Chebyshev-prefix rows, bad KKT stationarity rows,
bad proximal residual rows, negative-norm rows, and projection-orthogonality
examples graduate through
[QF_LRA / Farkas Evidence](../../proof-cookbook/recipes/qf-lra-farkas.md).
Finite vector-space, dual-space, module, ideal, and tensor-product equality
conflicts use
[QF_UF / Alethe Congruence Evidence](../../proof-cookbook/recipes/qf-uf-congruence-alethe.md)
when the key step is functional consistency or congruence. Integer boundary
matrix coefficient conflicts use
[QF_LIA / Diophantine Evidence](../../proof-cookbook/recipes/qf-lia-diophantine.md).
Rank-nullity, spectral theorems, Hilbert-space projection, Riesz
representation, conditioning, and convergence of numerical algorithms remain
[Lean Horizon](../../proof-cookbook/recipes/lean-horizon-template.md) or
explicit numerical-honesty work, not consequences of these finite rows.

## Horizon

General spectral theorems, rank theorems, vector-space dimension theorems,
duality and bidual theorems, Cauchy-Schwarz and Gram-Schmidt as general
theorems, Hilbert projection/Riesz representation results, topological duals,
module theory, universal coefficient theorem schemas, exact sequences,
Ext/Tor laws,
Chebyshev-system/Haar-space theorems, minimax approximation, conditioning,
numerical stability, SDP, general convex analysis, KKT sufficiency, constraint
qualifications, and algorithm convergence need proof routes or carefully
bounded numerical-experiment metadata.
