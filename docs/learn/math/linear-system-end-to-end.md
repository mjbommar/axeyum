# End To End: Linear System And LP Replay

This lesson follows exact rational linear-algebra and optimization resources
from data row to replayed result. It uses
[linear-algebra-rational-v0](../../../artifacts/examples/math/linear-algebra-rational-v0/)
and [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/).

Concept rows:

- `curriculum_linear_algebra`, `field_linear_algebra`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `matrix-vector-solution` | `sat` | replay-only |
| `singular-system-inconsistent` | `unsat` | replay-only |
| `objective-threshold-farkas-infeasible` | `unsat` | checked |

The first two rows are exact arithmetic replay. The LP threshold row carries a
tiny checked Farkas-style certificate.

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

## Replay

For the matrix row, the checker recomputes:

```text
[2*1 + 1*2, 1*1 + (-1)*2] = [4, -1]
```

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
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The untrusted side can search for vectors, LU factors, feasible points, or
certificates. The trusted checker recomputes matrix products, evaluates linear
constraints, and verifies certificate arithmetic over exact rationals.
