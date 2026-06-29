# End To End: Rational Midpoint

This lesson follows an exact rational witness from data row to replayed result.
It uses the [rationals-lra-v0](../../../artifacts/examples/math/rationals-lra-v0/)
pack.

Concept rows:

- `curriculum_rationals`, `curriculum_reals`, and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `density-between-witness` | `sat` | replay-only |
| `additive-inverse-witness` | `sat` | replay-only |
| `trichotomy-fixed-unsat` | `unsat` | checked |
| `order-transitivity-fixed-unsat` | `unsat` | checked |

The pack demonstrates exact rational replay. It does not claim a general proof
of density or order theory for all rationals. The two fixed `unsat` order rows
also route through Axeyum's `QF_LRA` Farkas evidence path.

## Encode

The density witness is:

```text
a = 1/3
b = 2/3
midpoint = 1/2
```

The claim is that `midpoint` lies strictly between `a` and `b`.

## Replay

The checker parses all three values as exact fractions and recomputes:

```text
(1/3 + 2/3) / 2 = 1/2
1/3 < 1/2 < 2/3
```

The witness is accepted because both the arithmetic identity and the order
constraints hold exactly.

## Farkas Checks

For the fixed trichotomy row, the pair is:

```text
left = 1/4
right = 3/4
```

Because `left < right`, a violation must take one of the impossible branches
`left >= right`, `left = right`, or `left > right`. The solver regression builds
each branch as a linear rational system and requires `UnsatFarkas` evidence.

For the fixed transitivity row, the checked violating branch is:

```text
a = 1/5
b = 2/5
c = 3/5
a < b
b < c
a >= c
```

The search result is not trusted by itself. The trusted part is the independent
Farkas certificate check over exact rational multipliers.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
cargo test -p axeyum-solver --test math_resource_lra_routes
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

A solver or writer can propose the midpoint. The trusted checker only performs
exact fraction arithmetic, comparisons, and Farkas certificate checks for the
fixed unsat branches. General real completeness and limit arguments remain
outside this pack.
