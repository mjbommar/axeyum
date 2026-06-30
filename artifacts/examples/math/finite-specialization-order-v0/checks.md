# Checks

## `specialization-preorder-witness`

Expected result: `sat`.

The validator recomputes the specialization preorder from open-set membership
and checks it matches the listed ordered pairs.

## `closure-characterization-witness`

Expected result: `sat`.

The validator recomputes singleton closures by finite closure/interior replay
and checks `x <= y` iff `x` is in `closure({y})`.

## `t0-poset-witness`

Expected result: `sat`.

The validator checks that the listed finite topology is `T0` by confirming the
specialization preorder is antisymmetric.

## `bad-t0-antisymmetry-rejected`

Expected result: `unsat`.

The indiscrete two-point topology makes `x` and `y` mutually specialize. The
bad row claims `T0`, so antisymmetry would force `x = y`; the source SMT-LIB
artifact also asserts `x != y`. Axeyum emits and checks an Alethe proof for
that fixed equality contradiction.

## `general-specialization-order-lean-horizon`

Expected result: `not-run`.

General specialization-order theory, T0 quotients, sober spaces, Alexandroff
spaces, and domain-theoretic topology remain Lean-horizon.
