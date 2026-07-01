# End To End: Finite-Dimensional Operators

This lesson follows one finite-dimensional operator resource from exact vector,
matrix, and recurrence replay to checked rejection of false finite claims. It uses the
[finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)
pack.

Concept rows:

- `field_functional_analysis_and_operator_theory`, `field_linear_algebra`,
  `field_numerical_analysis`, and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_linear_algebra`, `curriculum_reals`, and
  `curriculum_polynomials` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `family_exact_rational_farkas` in the atlas example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `l1-triangle-witness` | `sat` | replay-only |
| `bad-l1-sum-norm-rejected` | `unsat` | checked QF_LRA/Farkas |
| `matrix-operator-bound` | `sat` | replay-only |
| `chebyshev-recurrence-witness` | `sat` | replay-only |
| `bad-chebyshev-t3-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-operator-bound-rejected` | `unsat` | checked QF_LRA/Farkas |

Every row is finite-dimensional and exact-rational. The pack checks concrete
vectors, matrices, norms, and recurrence values. It does not prove Banach-space
theorems, compact-operator facts, infinite-dimensional spectral theory, or
general Chebyshev-space approximation theorems.

## Replay A Norm Inequality

The `l1` witness uses two vectors:

```text
u = (1, 2)
v = (3, -1)
u + v = (4, 1)
```

The checker recomputes the sum and the exact `l1` norms:

```text
||u||_1 = 3
||v||_1 = 4
||u + v||_1 = 5
```

Then it verifies the finite triangle inequality instance:

```text
5 <= 3 + 4
```

No solver result is trusted here. The row is accepted only because the small
exact-rational replay succeeds.

The bad norm row keeps the same replayed vectors but claims:

```text
||u + v||_1 <= 4
```

Replay computes `||u+v||_1 = 5`, so the committed SMT-LIB artifact
[`bad-l1-sum-norm-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-operator-v0/smt2/bad-l1-sum-norm-farkas-conflict.smt2)
isolates the final contradiction:

```text
sum_norm = 5
sum_norm <= 4
```

The checked certificate proves only this exact finite inequality conflict. It
does not prove the general triangle inequality for every normed space.

## Replay A Matrix Operator Bound

The operator witness uses the infinity norm and the matrix row-sum norm:

```text
A = [[1, -1],
     [2,  1]]
x = (2, -1)
```

Replay computes the image:

```text
A*x = (3, 3)
```

and the norms:

```text
||x||_infty = 2
||A*x||_infty = 3
||A||_row-sum = 3
```

The finite operator-bound row is therefore:

```text
||A*x||_infty <= ||A||_row-sum * ||x||_infty
3 <= 3 * 2
```

This is a concrete finite-dimensional calculation. It is not a theorem about
all normed spaces.

## Check The Bad Bound

The negative row reuses the same matrix-vector source object but claims:

```text
||A*x||_infty <= 2
```

Replay computes `||A*x||_infty = 3`, so the committed SMT-LIB artifact
[`bad-operator-bound-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-operator-v0/smt2/bad-operator-bound-farkas-conflict.smt2)
isolates the final contradiction:

```text
image_norm = 3
image_norm <= 2
```

The solver search and generated certificate are not trusted. The accepted
evidence is the independently checked `UnsatFarkas` certificate produced from
the source assertions.

## Replay A Chebyshev Recurrence

The polynomial recurrence row is also finite and exact. At `x = 1/2`, the pack
lists:

```text
T0 = 1
T1 = 1/2
T2 = -1/2
T3 = -1
```

The checker verifies the recurrence:

```text
T(n+1) = 2*x*T(n) - T(n-1)
```

for the listed finite prefix. General Chebyshev-system, Haar-space, and minimax
approximation theorems remain Lean-horizon material.

## Check The Bad Chebyshev Value

The bad Chebyshev row reuses the same finite prefix but claims:

```text
T3(1/2) = -1/2
```

Replay computes `T3(1/2) = -1`. The committed SMT-LIB artifact
[`bad-chebyshev-t3-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-operator-v0/smt2/bad-chebyshev-t3-farkas-conflict.smt2)
uses the equivalent shifted contradiction:

```text
t3_plus_one = 0
t3_plus_one = 1/2
```

The checked certificate proves only this exact finite recurrence-value
conflict.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_l1_sum_norm_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_operator_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_chebyshev_t3_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> proposed vector, matrix, recurrence values, or Farkas certificate
trusted small checking -> exact rational replay and exact Farkas arithmetic
remaining horizon -> Banach/Hilbert-space theorems, compact operators, and general approximation theory
```

For the broader bridge across dynamics, operators, Chebyshev systems, Markov
chains, and hitting times, read
[End To End: Bounded Dynamics And Operators](analysis-dynamics-end-to-end.md).
