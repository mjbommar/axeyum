# End To End: Spectral Linear Algebra

This lesson follows one exact finite spectral-linear-algebra resource from
eigenpair replay to an orthogonal eigenbasis, Rayleigh quotient,
spectral-decomposition reconstruction, checked bad-Rayleigh-quotient
rejection, and checked bad-eigenpair rejection.
It uses the
[spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`,
  `field_functional_analysis_and_operator_theory`,
  `field_numerical_analysis`, and `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `symmetric-eigenpair-witness` | `sat` | replay-only |
| `orthogonal-eigenbasis-witness` | `sat` | replay-only |
| `rayleigh-quotient-witness` | `sat` | replay-only |
| `bad-rayleigh-quotient-rejected` | `unsat` | checked |
| `spectral-decomposition-witness` | `sat` | replay-only |
| `bad-eigenpair-rejected` | `unsat` | checked |

All rows use one rational symmetric `2x2` matrix. The positive rows replay
finite exact-rational matrix arithmetic. The negative row rejects a false
eigenpair by recomputation.

## Replay An Eigenpair

The fixed matrix is:

```text
A = [[2, 1],
     [1, 2]]
```

The first witness records:

```text
lambda = 3
v = [1, 1]
A*v = [3, 3]
```

The validator recomputes both sides:

```text
A*v      = [2*1 + 1*1, 1*1 + 2*1] = [3, 3]
lambda*v = [3*1, 3*1]             = [3, 3]
```

So the eigenpair checks for this finite matrix.

## Replay An Orthogonal Eigenbasis

The listed eigenvalues and eigenvectors are:

```text
lambda_1 = 3, v_1 = [1,  1]
lambda_2 = 1, v_2 = [1, -1]
```

The validator checks each eigenpair and recomputes:

```text
v_1 . v_2 = 1*1 + 1*(-1) = 0
||v_1||^2 = 2
||v_2||^2 = 2
```

That gives an exact finite orthogonal eigenbasis witness for this symmetric
matrix.

## Replay A Rayleigh Quotient

For `v = [1,1]`, the validator recomputes:

```text
A*v = [3,3]
v^T*A*v = [1,1] . [3,3] = 6
v^T*v = 2
(v^T*A*v) / (v^T*v) = 3
```

This connects the eigenpair witness to a fixed Rayleigh quotient. It does not
claim optimization of the quotient over all vectors.

The bad Rayleigh row keeps the same replayed numerator and denominator but
claims:

```text
(v^T*A*v) / (v^T*v) = 4
```

After exact replay computes `3`, the source `QF_LRA` artifact exposes the final
quotient equality conflict:

```text
rayleigh_quotient = 3
rayleigh_quotient = 4
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Replay Spectral Decomposition

The decomposition row uses:

```text
P = [[1,  1],
     [1, -1]]

D = [[3, 0],
     [0, 1]]

P^-1 = [[1/2,  1/2],
        [1/2, -1/2]]
```

The validator first checks `P * P^-1 = I`, then reconstructs:

```text
P*D*P^-1 = [[2, 1],
            [1, 2]]
```

Every multiplication is exact rational matrix replay.

## Reject A Bad Eigenpair

The bad row claims that the same vector has eigenvalue `2`:

```text
claimed lambda = 2
v = [1,1]
```

The validator recomputes:

```text
A*v = [3,3]
2*v = [2,2]
```

The spectral pack exposes the first component as a `QF_LRA` contradiction:

```text
eigen_image_0 = 3
eigen_image_0 = 2
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

The two vectors differ, so the false eigenpair claim is checked `unsat`.

## Name The Horizon

The pack does not claim broad spectral theory:

```text
spectral theorem in arbitrary finite dimension
compact-operator spectral theory
numerical eigensolver correctness
spectral convergence
Rayleigh-Ritz optimization theorems
```

Those require Lean resources, proof-producing spectral certificates, or
carefully scoped numerical metadata. This pack only checks finite rational
matrix evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
cargo test -p axeyum-solver --test math_resource_lra_routes spectral_bad_rayleigh_quotient_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current spectral-linear-algebra resource pattern:

```text
untrusted fast search -> eigenpair, basis, quotient, or decomposition candidate
trusted small checking -> exact rational matrix-vector and matrix-matrix replay
proof upgrade -> QF_LRA/Farkas certificate for false quotient/eigenpair claims
remaining horizon -> general spectral, compact-operator, and numerical proofs
```

The graduation route is deterministic exact-rational finite-matrix checking
plus checked proof objects for false spectral claims before broader spectral
theorems or numerical eigensolver claims are promoted.
