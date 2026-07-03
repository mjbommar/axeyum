# Checks

## Replay-Only Witness Rows

`cluster-assignment-witness`
: Confirms that the committed dataset and cluster labels define two nonempty
  clusters with the listed memberships.

`centroid-witness`
: Recomputes each centroid as the exact coordinate-wise average of its assigned
  points.

`within-cluster-energy-witness`
: Recomputes each assigned residual vector, squared distance, per-cluster
  WCSS, and total WCSS.

`variance-decomposition-witness`
: Recomputes the global centroid, total squared deviation,
  between-cluster sum-of-squares, and the finite identity
  `total = within + between`.

`bad-centroid-x-rejected`
: Rejects the malformed replay-only claim that the first centroid x-coordinate
  is `-1/2` when the exact committed data force `-1`.

## Checked Evidence Row

`qf-lra-bad-centroid-x`
: Uses the source SMT-LIB artifact
  `smt2/bad-centroid-x-farkas-conflict.smt2` to check that
  `2*c0x = -2` and `c0x = -1/2` are linearly inconsistent.

## Theorem Horizon

`general-k-means-clustering-theory-lean-horizon`
: Records that Lloyd convergence, global optimality, NP-hardness, clustering
  consistency, initialization guarantees, and floating-point implementation
  correctness are not proved by this finite exact resource.
