# Checks

## `permutation-count-fixed`

Expected result: `sat`.

The witness checks the fixed count:

```text
P(5, 3) = 5 * 4 * 3 = 60
```

## `pascal-identity-fixed`

Expected result: `sat`.

The witness checks Pascal's identity at `n = 6`, `k = 3`:

```text
C(6, 3) = C(5, 2) + C(5, 3)
20 = 10 + 10
```

## `pigeonhole-3-2-unsat`

Expected result: `unsat`.

The checked query is the existence of an injective placement of three pigeons
into two holes. The validator enumerates all `2^3` placements and confirms each
has a collision.
