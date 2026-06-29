# Checks

## `f2-plane-vector-space`

Expected result: `sat`.

The validator checks that the listed field, vector addition, and scalar
multiplication tables satisfy the finite vector-space laws.

## `subspace-span-replay`

Expected result: `sat`.

The validator checks that `{00, 10}` contains zero, is closed under addition
and scalar multiplication, equals the span of `10`, and has dimension `1`.

## `linear-map-kernel-image`

Expected result: `sat`.

The validator checks that the projection preserves addition and scalar
multiplication, then recomputes its kernel and image.

## `rank-nullity-replay`

Expected result: `sat`.

The validator derives dimensions from finite cardinalities over `F2` and checks
`dim(domain) = dim(kernel) + dim(image)`.

## `bad-subspace-rejected`

Expected result: `unsat`.

The validator rejects `{00, 10, 01}` because `10 + 01 = 11`, and `11` is not in
the subset.

## `general-vector-space-theory-lean-horizon`

Expected result: `not-run`.

Basis extension, dimension uniqueness, quotient spaces, arbitrary-field
rank-nullity, module theory, and infinite-dimensional vector spaces belong in
future Lean resources. The finite rows above are exact table replay checks
only.
