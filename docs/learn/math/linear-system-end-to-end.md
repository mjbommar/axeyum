# End To End: Linear System And LP Replay

This lesson follows exact rational linear-algebra and optimization resources
from data row to replayed result. It uses
[linear-algebra-rational-v0](../../../artifacts/examples/math/linear-algebra-rational-v0/)
and [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/).
For the LP-only first-principles view, read
[End To End: Linear Optimization](linear-optimization-end-to-end.md).

Concept rows:

- `curriculum_linear_algebra`, `field_linear_algebra`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `matrix-vector-solution` | `sat` | replay-only |
| `lu-factorization-witness` | `sat` | replay-only |
| `bad-lu-product-entry-rejected` | `unsat` | checked |
| `singular-system-inconsistent` | `unsat` | checked |
| `objective-threshold-farkas-infeasible` | `unsat` | checked |

The matrix-vector and positive LU rows are exact arithmetic replay. The bad LU
product entry, inconsistent system, and LP threshold rows carry checked Farkas
evidence for fixed linear rational systems.

## Encode

The matrix-vector witness is:

```text
A = [[2, 1],
     [1,-1]]
x = [1, 2]
b = [4,-1]
```

The Farkas certificate for `x + y >= 5` over the base LP region uses two
constraints:

```text
budget:            x + y <= 4
threshold-negated: -x - y <= -5
```

with multipliers `1` and `1`.
The solver regression builds those same inequalities and requires rechecked
`UnsatFarkas` evidence, so the pack-local arithmetic check is not the only
trusted artifact.

The singular linear-system row is:

```text
x + y = 1
2*x + 2*y = 3
```

The row-scaling replay observes that the second left-hand side is twice the
first while `3 != 2*1`. The solver regression builds the same equations as
`QF_LRA` and requires rechecked `UnsatFarkas` evidence.

The LU row uses:

```text
A = [[2, 1],
     [4, 3]]
L = [[1, 0],
     [2, 1]]
U = [[2, 1],
     [0, 1]]
```

The positive row recomputes `L*U = A`. The checked negative row isolates the
bottom-right product entry: exact replay gives `(L*U)[1,1] = 3`, while the
malformed claim says that same entry is `4`.

## Replay

For the matrix row, the checker recomputes:

```text
[2*1 + 1*2, 1*1 + (-1)*2] = [4, -1]
```

For the bad LU row, the checker recomputes:

```text
(L*U)[1,1] = 2*1 + 1*1 = 3
```

The source SMT-LIB artifact then forces the same product entry to equal both
`3` and `4`, and the route regression requires independently rechecked
`UnsatFarkas` evidence.

For the Farkas row, the checker combines the two inequalities:

```text
(x + y) + (-x - y) <= 4 + (-5)
0 <= -1
```

The combined coefficients cancel and the bound is contradictory, so the fixed
threshold claim is checked `unsat`.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
cargo test -p axeyum-solver --test math_resource_lra_routes linear_algebra_bad_lu_product_entry_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes linear_algebra_singular_system_inconsistent_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_emits_checked_farkas
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for vectors, LU factors, feasible points, or
certificates. The trusted checker recomputes matrix products, evaluates linear
constraints, and verifies Farkas certificate arithmetic over exact rationals.
