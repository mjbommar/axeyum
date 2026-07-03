# Exact Finite Principal Component Checks

This pack is for learners, proof contributors, solver contributors, and
resource consumers who need a small PCA-style example with an explicit trust
boundary.

The fixed object is a four-row rational sample. The replay checks its mean,
centered rows, covariance matrix, principal eigenpair, projected scores, and
one-component residual energy exactly. A separate QF_LRA/Farkas row rejects a
malformed principal-eigenvalue claim.

## Audience

- Learners: see one PCA-like computation without floating-point ambiguity.
- Educators: show what a finite exact PCA shadow can and cannot prove.
- Proof contributors: inspect the Farkas route for the bad eigenvalue row.
- Solver contributors: reuse a compact rational spectral/statistics artifact.
- Consumers: query the pack by statistics, linear algebra, numerical analysis,
  optimization, eigenpair, covariance, or PCA-shadow concepts.

## Scope

The pack checks this finite rational sample:

```text
(-2,  0)
( 2,  0)
( 0, -1)
( 0,  1)
```

It validates:

- mean and centered rows;
- centered Gram and covariance matrices;
- principal and secondary eigenpairs;
- principal projected scores;
- one-component reconstruction and residual energy;
- a checked rejection of the false claim `lambda = 3/2`.

## Limitations

This is not a proof of general PCA, SVD, explained-variance optimality, sample
estimator consistency, perturbation theory, or floating-point PCA
implementation correctness. Those remain Lean/theorem or numerical-honesty
horizon work.

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-principal-components-v0

cargo test -p axeyum-solver --test math_resource_lra_routes finite_principal_components_bad_eigenvalue_artifact_emits_checked_farkas
```
