# Checks

## Replay-Only Rows

`sample-mean-centering-witness`

: Recomputes the sample mean and centered rows exactly.

`covariance-matrix-witness`

: Recomputes the centered Gram matrix, covariance matrix, and total variance.

`principal-eigenpair-witness`

: Checks `C v1 = lambda1 v1`, `C v2 = lambda2 v2`, and the principal
  eigenvalue ordering for this fixed diagonal covariance matrix.

`projection-reconstruction-witness`

: Recomputes principal scores, one-component reconstruction, residual rows,
  principal energy, residual energy, and explained-variance ratio.

`bad-principal-eigenvalue-rejected`

: Replays the principal eigenpair and rejects the false claim that the
  principal eigenvalue is `3/2`.

## Checked Row

`qf-lra-bad-principal-eigenvalue`

: Parses
  `smt2/bad-principal-eigenvalue-farkas-conflict.smt2`, emits
  `UnsatFarkas` evidence, and independently checks the certificate through the
  shared `math_resource_lra_routes` regression.

## Horizon Row

`general-pca-spectral-theory-lean-horizon`

: Records that general PCA/SVD optimality, estimator consistency, perturbation
  theory, randomized algorithms, and floating-point PCA implementations are not
  proved by this finite exact resource.
