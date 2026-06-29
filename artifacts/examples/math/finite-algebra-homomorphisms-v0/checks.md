# Checks

## `z4-to-z2-group-homomorphism`

Expected result: `sat`.

The validator checks every pair in `Z/4Z` and confirms that reducing modulo `2`
preserves addition.

## `kernel-image-replay`

Expected result: `sat`.

The validator recomputes the kernel as the preimage of the codomain identity
and the image as the range of the map.

## `quotient-first-isomorphism-replay`

Expected result: `sat`.

The validator checks the listed cosets, quotient operation, induced map,
bijectivity onto the image, and homomorphism preservation.

## `z4-to-z2-ring-homomorphism`

Expected result: `sat`.

The validator checks zero preservation, one preservation, addition
preservation, and multiplication preservation for every pair.

## `bad-group-homomorphism-rejected`

Expected result: `unsat`.

The validator rejects the malformed map because `1 + 1 = 2`, the map sends
`2` to `1`, but the codomain sum `f(1) + f(1)` is `0`.

## `general-isomorphism-theorems-lean-horizon`

Expected result: `not-run`.

General group and ring isomorphism theorems, normal-subgroup/ideal quotient
theory, module homomorphisms, and categorical universal properties belong in
future Lean resources. The finite rows above are exact table replay checks
only.
