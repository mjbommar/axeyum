# End To End: Numerical Linear Algebra

This lesson follows one exact numerical-linear-algebra resource from residual
norm replay to a rational solution box, a one-step Jacobi contraction check,
and a checked bad residual-bound rejection. It uses the
[numerical-linear-algebra-v0](../../../artifacts/examples/math/numerical-linear-algebra-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_numerical_analysis`, `field_linear_algebra`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `residual-norm-bound-witness` | `sat` | replay-only |
| `solution-box-replay` | `sat` | replay-only |
| `jacobi-contraction-witness` | `sat` | replay-only |
| `bad-residual-bound-rejected` | `unsat` | checked |

The pack uses exact rational arithmetic only. It models the algebra under
numerical linear algebra without making floating-point stability or broad
convergence claims.

## Replay A Residual Norm Bound

The residual witness uses:

```text
A = [[4, 1],
     [2, 3]]
x_hat = [1, 1]
b = [6, 6]
```

The validator recomputes:

```text
A*x_hat = [5, 5]
residual = A*x_hat - b = [-1, -1]
||residual||_infty = 1
```

The claimed bound is `1`, so this finite residual certificate checks.

## Replay A Solution Box

The exact solution row records:

```text
x = [6/5, 6/5]
box = [1, 3/2] x [1, 3/2]
```

The validator checks both the equation and interval membership:

```text
A*x = [6, 6]
residual = [0, 0]
1 <= 6/5 <= 3/2
```

This is exact interval-box replay, not a floating-point enclosure theorem.

## Replay A Jacobi Step

The Jacobi row uses a diagonally dominant system:

```text
A = [[4, 1],
     [1, 3]]
b = [1, 2]
x_0 = [0, 0]
```

The first Jacobi step is:

```text
x_1 = [1/4, 2/3]
```

The exact solution is:

```text
x* = [1/11, 7/11]
```

The validator recomputes the infinity-norm errors:

```text
||x_0 - x*||_infty = 7/11
||x_1 - x*||_infty = 7/44
```

and checks the one-step contraction bound:

```text
7/44 <= (1/3) * (7/11)
```

This is a single exact replayed step. General iterative-method convergence is
still a proof horizon.

## Reject A Bad Residual Bound

The bad row reuses the first residual example and claims:

```text
||A*x_hat - b||_infty <= 1/2
```

The trusted checker recomputes:

```text
||A*x_hat - b||_infty = 1
```

Since `1` is not at most `1/2`, the false residual-bound claim is checked
`unsat`.

## Name The Horizon

The pack does not claim broad numerical analysis:

```text
floating-point rounding models
backward-error analysis
conditioning theorems
stable LU/QR algorithms
general iterative-method convergence
numerical stopping criteria
```

Those need a numerical-honesty schema, proof-producing interval or Farkas-style
certificates, Lean proofs, or explicit reproducibility metadata. This pack only
checks exact rational finite-matrix obligations.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current numerical-linear-algebra resource pattern:

```text
untrusted fast search -> residual, box, iterate, or bad-bound candidate
trusted small checking -> exact rational matrix, norm, and interval replay
remaining horizon -> floating-point, stability, conditioning, and convergence
```

The graduation route is deterministic exact-rational checking plus emitted
proof objects for bad bounds before floating-point or algorithmic convergence
claims are promoted.
