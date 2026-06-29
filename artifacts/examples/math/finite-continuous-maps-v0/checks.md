# Checks

## `finite-continuous-map-witness`

Expected result: `sat`.

The validator checks every codomain open set and confirms its preimage is open
in the domain.

## `open-preimage-witness`

Expected result: `sat`.

The validator recomputes the preimage of `{v}` as `{1}` and checks that `{1}` is
open in the Sierpinski domain.

## `finite-homeomorphism-witness`

Expected result: `sat`.

The validator checks that the map is bijective, continuous, and has a
continuous inverse.

## `bad-continuous-map-rejected`

Expected result: `unsat`.

The validator rejects continuity for the map into the discrete topology because
the codomain open set `{u}` has preimage `{0}`, which is not domain-open.

## `bad-homeomorphism-claim-rejected`

Expected result: `unsat`.

The validator rejects the homeomorphism claim because the bijection is not
continuous.

## `general-continuous-map-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general continuous-map theorems. Continuous
images of compact or connected spaces and homeomorphism-invariance theorems
need a future Lean artifact with no `sorryAx` dependencies.
