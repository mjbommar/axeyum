# Checks

## `density-between-witness`

Expected result: `sat`.

The witness `1/2` lies strictly between `1/3` and `2/3`, and is exactly their
average.

## `additive-inverse-witness`

Expected result: `sat`.

The witness `-5/7` is the additive inverse of `5/7`.

## `trichotomy-fixed-unsat`

Expected result: `unsat`.

The checked query is the absence of a trichotomy violation for the fixed pair
`1/4` and `3/4`.

The resource-backed Axeyum regression parses one source SMT-LIB artifact per
impossible non-less, equality, and greater-than branch as `QF_LRA` systems and
requires each one to return rechecked `UnsatFarkas` evidence.

## `order-transitivity-fixed-unsat`

Expected result: `unsat`.

The checked query is the absence of a transitivity violation for the fixed chain
`1/5 < 2/5 < 3/5`.

The resource-backed Axeyum regression parses a source SMT-LIB artifact that
adds the violating branch `1/5 >= 3/5` to the fixed chain and requires
rechecked `UnsatFarkas` evidence.
