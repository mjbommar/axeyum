# End To End: Conditional Probability

This lesson follows a finite probability resource from atom table to replayed
conditional probability. It uses the
[finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/)
pack.

Concept rows:

- `field_probability_theory`, `field_statistics`, and `field_measure_theory` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting` and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `pmf-total-mass` | `sat` | replay-only |
| `conditional-probability-witness` | `sat` | replay-only |
| `bayes-posterior-witness` | `sat` | replay-only |

Every check is exact finite replay over rational numbers.

## Encode

The conditional-probability witness is a four-atom joint table:

```text
rain_late    = 1/10
rain_on_time = 1/5
dry_late     = 1/5
dry_on_time  = 1/2
```

The claimed query is:

```text
P(late | rain) = 1/3
```

## Replay

The checker recomputes:

```text
P(rain) = 1/10 + 1/5 = 3/10
P(late and rain) = 1/10
P(late | rain) = (1/10) / (3/10) = 1/3
```

It also checks that the table is normalized and that every atom probability is
in `[0,1]`.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The search side may propose a probability table or posterior. The trusted side
only recomputes finite sums and exact rational divisions. Continuous
probability, convergence, and statistical inference are outside this proof
claim.
