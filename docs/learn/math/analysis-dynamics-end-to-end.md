# End To End: Bounded Dynamics And Operators

This lesson follows bounded analysis-adjacent resources from data row to
replayed result. It uses
[bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/) and
[finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/).

Concept rows:

- `field_differential_equations_and_dynamical_systems`,
  `field_functional_analysis_and_operator_theory`, `field_numerical_analysis`,
  and `field_linear_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `bounded-invariant-witness` | `sat` | replay-only |
| `unsafe-threshold-reachable` | `sat` | replay-only |
| `matrix-operator-bound` | `sat` | replay-only |
| `chebyshev-recurrence-witness` | `sat` | replay-only |

These are bounded finite traces and finite-dimensional algebra checks, not
general analysis theorems.

## Encode

The invariant witness is a fixed recurrence trace:

```text
x(0) = 0
x(t+1) = x(t) + 2
trace = 0, 2, 4, 6, 8
invariant = 0 <= x(t) <= 8
```

The operator witness is a fixed matrix-vector calculation:

```text
A = [[1,-1],
     [2, 1]]
x = [2,-1]
A*x = [3,3]
||x||_infty = 2
||A||_row-sum = 3
||A*x||_infty = 3
```

## Replay

For the dynamics row, the checker verifies every transition:

```text
0 -> 2 -> 4 -> 6 -> 8
```

and then checks every state lies in `[0,8]`.

For the operator row, the checker recomputes `A*x`, the infinity norms, the
row-sum norm, and the bound:

```text
||A*x||_infty = 3 <= 3 * 2 = 6
```

For the Chebyshev row, it checks the finite recurrence at `x = 1/2`:

```text
T0 = 1
T1 = 1/2
T2 = -1/2
T3 = -1
```

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The trusted checker handles finite traces, exact rational matrices, and finite
recurrence lists. General limits, ODE existence and uniqueness, stability,
compact operators, Banach/Hilbert-space theorems, and general Chebyshev spaces
remain Lean-horizon material.
