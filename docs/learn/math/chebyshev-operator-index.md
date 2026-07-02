# Chebyshev And Operator Replay Index

This index keeps the functional-analysis/operator resources grounded in finite
exact arithmetic. It connects finite-dimensional operator bounds, Chebyshev
recurrence values, interpolation matrices, alternating residuals, spectral
rows, and characteristic-polynomial checks without turning them into
Banach-space, Hilbert-space, compact-operator, minimax, or general Chebyshev
theorems.

The trust pattern is:

```text
untrusted fast search -> candidate operator bound, grid, coefficients, residual, or spectrum
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
remaining horizon -> infinite-dimensional and approximation-theory theorems
```

## Concept Rows

- `bridge_finite_operator_chebyshev`
- `bridge_inner_product_projection`
- `bridge_residual_bound`
- `bridge_eigenpair`
- `bridge_characteristic_polynomial`
- `bridge_qf_lra_farkas_anatomy`
- `field_functional_analysis_and_operator_theory`
- `field_numerical_analysis`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_linear_algebra`
- `curriculum_polynomials`
- `curriculum_reals`
- `curriculum_rationals`

These rows live in the
[Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json).

## Resource Map

| Question | Packs | Trusted Check | Horizon |
|---|---|---|---|
| Does a finite operator/norm row replay? | `finite-operator-v0` | vector-sum replay, exact `l1` norm, matrix-vector replay, exact infinity norm, row-sum bound, replay-only bad norm/bound rows, and separate checked `qf-lra-*` Farkas rows | Banach/Hilbert-space operator theory |
| Does a Chebyshev recurrence prefix replay? | `finite-operator-v0` | fixed rational recurrence values such as `T0`, `T1`, `T2`, `T3` at `x = 1/2`, plus replay-only bad `T3` rejection and a separate checked `qf-lra-bad-chebyshev-t3` row | general Chebyshev polynomial theory |
| Is a finite interpolation grid unisolvent? | `finite-chebyshev-systems-v0` | exact Vandermonde matrix and determinant replay | Haar-space and Chebyshev-system theorems |
| Do finite samples match listed coefficients? | `finite-chebyshev-systems-v0` | exact evaluation-matrix times coefficient-vector replay plus checked bad-sample Farkas row | general interpolation and approximation theory |
| Does a residual alternate on a finite grid? | `finite-chebyshev-systems-v0` | exact residual values, signs, common absolute error, and checked bad-uniform-error Farkas row | minimax and alternation theorems |
| Do spectral or characteristic-polynomial rows share the same route? | `spectral-linear-algebra-v0`, `matrix-invariants-v0` | exact matrix arithmetic plus checked Farkas rows for bad Rayleigh-quotient, eigenpair, or characteristic-polynomial claims | spectral theorem and general Cayley-Hamilton claims |

## Checkable Shapes

Finite operator rows are exact rational vector and matrix calculations:

```text
u = [1, 2]
v = [3, -1]
u + v = [4, 1]
||u + v||_1 = 5
claimed_l1_bound = 4

A = [[1, 2],
     [0, 3]]
x = [1, 1]
A*x = [3, 3]
||A*x||_infty = 3
claimed_upper_bound = 2
```

The validator recomputes the vector sum, matrix image, and norms before the
final contradiction is handed to the QF_LRA/Farkas route. The certificate
checks the small rational conflict; it does not prove a general operator-norm
theorem.

The finite Chebyshev recurrence prefix is equally small:

```text
x = 1/2
T0, T1, T2, T3 = 1, 1/2, -1/2, -1
false claim: T3 = -1/2
```

After replay computes `T3 = -1`, the checked Farkas artifact uses the shifted
conflict `T3+1 = 0` versus `T3+1 = 1/2`.

Finite Chebyshev-system rows use an explicit grid and basis:

```text
points = -1, 0, 1
basis = 1, x, x^2
det(evaluation_matrix) = 2
```

The bad duplicate-node row keeps the finite source object just as small:

```text
points = 0, 0, 1
actual determinant = 0
claimed determinant = 1
```

That final determinant conflict is checked by the same exact-rational Farkas
route after replay exposes the bad claim.

The bad interpolation-sample row uses the ordinary coefficient replay:

```text
p(x) = 2 - x + 3*x^2
p(1) = 4
false claim: p(1) = 5
```

After finite replay computes `4`, the final sample-value conflict is another
checked QF_LRA/Farkas row.

The alternation row is also finite:

```text
r(x) = -1/2 + x^2
r(-1), r(0), r(1) = 1/2, -1/2, 1/2
```

This is an alternation-style witness on three listed points, not a proof of the
minimax alternation theorem.

The bad alternation row keeps the same replayed residual table and rejects the
false common-error claim:

```text
uniform_error = 1/2
false claim: uniform_error = 2/3
```

After finite replay computes `1/2`, the final uniform-error conflict is checked
as a QF_LRA/Farkas row.

## Use The Lessons

Start with [Finite-Dimensional Operators](finite-operator-end-to-end.md) for
exact vector norms, matrix row-sum bounds, Chebyshev recurrence replay, and the
split bad norm, bad operator-bound, and bad Chebyshev-prefix rows: exact replay
rejects the fixed values, while explicit `qf-lra-*` rows own checked Farkas
evidence.

Use [Rational Inner Product Spaces](inner-product-spaces-end-to-end.md) when the
operator story needs projection arithmetic, residual orthogonality, and checked
bad projection-orthogonality evidence.

Then read [Finite Chebyshev Systems](finite-chebyshev-systems-end-to-end.md)
for Vandermonde unisolvence, interpolation values, alternating residuals, and
checked duplicate-node, bad interpolation-sample, and bad alternation-magnitude
rejection.

Use [Matrix Computation Index](matrix-computation-index.md) when you want the
surrounding matrix-resource cluster: residuals, projections, eigenpairs,
characteristic polynomials, random matrices, chain/cochain matrices, modules,
tensors, operators, and Chebyshev systems.

Use [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
when you need the theorem boundary across analysis, topology, measure,
dynamics, and functional analysis.

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py concepts --field functional_analysis_and_operator_theory --text Chebyshev --require-any
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_operator_chebyshev --route Farkas --require-any
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_operator_chebyshev --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-chebyshev-t3 --require-any
python3 scripts/query-foundational-resources.py checks --field functional_analysis_and_operator_theory --route Farkas --proof-status checked --require-any
```

## Replay It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
```

Expected shape:

```text
validated 1 foundational example pack(s)
```

for each command.

## Trust Boundary

The checked rows prove only the listed finite rational rows: matrix actions,
norms, recurrence values, interpolation matrices, determinants, residual signs,
eigenpair arithmetic, characteristic-polynomial arithmetic, and bad finite
recurrence-value conflicts. They do not
prove Banach-space completeness, Hilbert projection, Riesz representation,
compact-operator facts, spectral theorem variants, Haar-space theorems,
minimax approximation, alternation theorems, or infinite-dimensional
Chebyshev-space results. Those remain Lean-horizon work until there are
kernel-checked proof artifacts.
