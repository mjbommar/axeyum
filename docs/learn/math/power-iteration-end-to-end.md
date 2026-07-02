# End To End: Finite Power Iteration

This lesson follows one exact finite power-iteration resource from two
matrix-vector steps through normalization, a Rayleigh quotient, a residual
shadow, a dominant eigenpair shadow, and a checked bad-coordinate rejection.
It uses the
[finite-power-iteration-v0](../../../artifacts/examples/math/finite-power-iteration-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_numerical_analysis`, and
  `field_functional_analysis_and_operator_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_eigenpair` and `bridge_residual_bound` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `first-power-step-replay` | `sat` | replay-only |
| `second-power-step-replay` | `sat` | replay-only |
| `normalized-iterate-replay` | `sat` | replay-only |
| `rayleigh-quotient-replay` | `sat` | replay-only |
| `residual-shadow-replay` | `sat` | replay-only |
| `dominant-eigenpair-shadow-replay` | `sat` | replay-only |
| `bad-power-iterate-coordinate-rejected` | `unsat` | replay-only |
| `qf-lra-bad-power-iterate-coordinate` | `unsat` | checked |
| `general-power-iteration-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses one rational diagonal matrix:

```text
A = [[2, 0],
     [0, 1]]
```

## Replay Two Power Steps

Starting from `v0 = [1,1]`, exact matrix-vector replay gives:

```text
v1 = A*v0 = [2,1]
v2 = A*v1 = [4,1]
```

The validator recomputes both products from the matrix and source vectors.
There is no floating-point rounding and no hidden numerical routine in this
step.

## Replay A Normalized Iterate

The pack records one finite normalization of the second iterate:

```text
||v2||_1 = |4| + |1| = 5
v2 / ||v2||_1 = [4/5, 1/5]
```

This is useful as an exact shadow of normalized power iteration. It is not a
claim about convergence of all normalized iterates.

## Replay A Rayleigh Quotient

For the first iterate `w = [2,1]`, the validator computes:

```text
A*w = [4,1]
w^T*A*w = 2*4 + 1*1 = 9
w^T*w = 2*2 + 1*1 = 5
rho(w) = 9/5
```

This links the iterate to the spectral vocabulary already used by the
spectral-linear-algebra pack.

## Replay A Residual Shadow

Using `lambda = 9/5`, the validator recomputes:

```text
A*w - lambda*w = [4,1] - [18/5,9/5]
                 = [2/5,-4/5]
```

The exact infinity norm is:

```text
max(|2/5|, |-4/5|) = 4/5
```

That is a finite residual check. It does not prove a residual-to-eigenvalue
error theorem.

## Replay The Dominant Eigenpair Shadow

For the same matrix:

```text
A*[1,0] = [2,0] = 2*[1,0]
```

The pack records this as the exact dominant eigenpair shadow for the finite
example.

## Reject A Bad Iterate Coordinate

The bad source row claims:

```text
second_iterate_x0 = 3
```

Exact replay computes:

```text
second_iterate_x0 = 4
```

The checked `QF_LRA` artifact isolates the scalar contradiction:

```text
power_iterate2_x0 = 4
power_iterate2_x0 = 3
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass independent
certificate checking.

## Name The Horizon

This pack does not claim:

```text
power-iteration convergence
spectral-gap sufficiency
Rayleigh quotient convergence
residual-to-eigenvalue error bounds
deflation or block iteration correctness
floating-point eigensolver stability
```

Those require Lean theorem statements, proof-producing spectral certificates,
or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-power-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_power_iteration_bad_coordinate_artifact_emits_checked_farkas
```

Expected output from the pack validator:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate iterates, quotient, residual, or eigenpair
trusted small checking -> exact rational matrix-vector and scalar replay
proof upgrade -> QF_LRA/Farkas certificate for the false coordinate claim
remaining horizon -> convergence, perturbation, and floating-point proofs
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false finite claims before broader eigensolver
or convergence claims are promoted.
