# End To End: Finite Jordan Chain

This lesson follows one exact Jordan-chain resource from eigenvector replay to
generalized-eigenvector replay, nilpotent-part checking, Jordan
reconstruction, and a checked bad-component rejection. It uses the
[finite-jordan-chain-v0](../../../artifacts/examples/math/finite-jordan-chain-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and
  `curriculum_polynomials` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_abstract_algebra`, and
  `field_functional_analysis_and_operator_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_eigenpair`, `bridge_characteristic_polynomial`, and
  `bridge_finite_operator_chebyshev` in the atlas

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `jordan-eigenvector-replay` | `sat` | replay-only |
| `generalized-eigenvector-replay` | `sat` | replay-only |
| `nilpotent-part-replay` | `sat` | replay-only |
| `jordan-reconstruction-replay` | `sat` | replay-only |
| `bad-jordan-chain-rejected` | `unsat` | replay-only |
| `qf-lra-bad-jordan-chain` | `unsat` | checked |
| `general-jordan-theory-lean-horizon` | `not-run` | Lean horizon |

The pack uses exact rational arithmetic only. It does not certify the Jordan
normal form theorem, diagonalization criteria, algebraic/geometric
multiplicity theory, or numerical eigensolver behavior.

## Replay The Eigenvector

The fixed matrix is:

```text
A = [[2, 1],
     [0, 2]]
```

with `lambda = 2` and `v1 = [1,0]`. The validator recomputes:

```text
A*v1 = [2,0]
2*v1 = [2,0]
```

So `v1` is an eigenvector for this finite matrix.

## Replay The Generalized Eigenvector

The nilpotent part is:

```text
N = A - 2I = [[0, 1],
              [0, 0]]
```

For `v2 = [0,1]`, the validator checks:

```text
N*v2 = [1,0] = v1
A*v2 = [1,2] = 2*v2 + v1
```

That is the finite Jordan-chain witness. It demonstrates generalized
eigenvector arithmetic for one fixed block, not the theorem that every matrix
has a Jordan form.

## Replay The Nilpotent Part

The validator recomputes `N = A - 2I`, checks that `N` is nonzero, and checks:

```text
N^2 = [[0,0],
       [0,0]]
```

This is the finite nilpotent-shadow part of the pack.

## Replay Jordan Reconstruction

The reconstruction row is intentionally small:

```text
P = I
J = [[2, 1],
     [0, 2]]
P^-1 = I
```

The validator checks:

```text
P*P^-1 = I
P*J*P^-1 = A
```

Every multiplication is exact rational matrix replay.

## Reject A Bad Jordan-Chain Component

The malformed row claims:

```text
first component of N*v2 = 0
```

Exact replay computes:

```text
N*v2 = [1,0]
```

The separate checked row isolates the final contradiction as `QF_LRA`:

```text
nilpotent_image_0 = 1
nilpotent_image_0 = 0
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Boundary

This pack is useful because it shows a nonsymmetric, non-diagonal Jordan-chain
shape that the symmetric spectral and SVD packs do not cover. The checked claim
is only the rational matrix, eigenvector, generalized vector, nilpotent part,
reconstruction, and final scalar contradiction.

General Jordan normal form, algebraic/geometric multiplicity theory,
diagonalization criteria, generalized eigenspace decomposition, and numerical
eigensolver behavior remain theorem or numerical-honesty horizons.

Run the focused checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-jordan-chain-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_jordan_chain_bad_component_artifact_emits_checked_farkas
```
