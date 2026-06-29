# End To End: Conditional Probability, Product Measures, And Finite Expectation

This lesson follows finite probability resources from atom tables to replayed
conditional probability, exact product measures, and finite expectations. It
uses the [finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/),
[finite-product-measure-v0](../../../artifacts/examples/math/finite-product-measure-v0/),
and [finite-integration-v0](../../../artifacts/examples/math/finite-integration-v0/)
packs.

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
| `product-measure-table-witness` | `sat` | replay-only |
| `marginalization-witness` | `sat` | replay-only |
| `finite-fubini-witness` | `sat` | replay-only |
| `bad-product-measure-rejected` | `unsat` | checked |
| `simple-function-integral-witness` | `sat` | replay-only |
| `bad-expectation-rejected` | `unsat` | checked |

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

The finite integration witness is a three-atom table:

```text
P(low) = 1/4
P(mid) = 1/4
P(high) = 1/2
f(low), f(mid), f(high) = 0, 2, 4
```

The product-measure witness crosses a fair coin with a fair three-sided die:

```text
P(heads) = P(tails) = 1/2
Q(one) = Q(two) = Q(three) = 1/3
R(x,y) = P(x) * Q(y)
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

For the integration row, the checker recomputes:

```text
integral f dP = 0*(1/4) + 2*(1/4) + 4*(1/2) = 5/2
```

It also checks an indicator integral, finite linearity, and rejects the false
claim `integral f dP = 3`.

For the product-measure row, the checker recomputes:

```text
R(heads, one) = (1/2) * (1/3) = 1/6
R({heads} x {two, three}) = 1/3
sum_y R(heads, y) = 1/2
sum_x R(x, two) = 1/3
```

For the finite Fubini row, it checks the direct finite sum and both iterated
sums over the same product table:

```text
sum_(x,y) f(x,y) R(x,y) = 3
sum_x P(x) * sum_y f(x,y) Q(y) = 3
sum_y Q(y) * sum_x f(x,y) P(x) = 3
```

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The search side may propose a probability table or posterior. The trusted side
only recomputes finite sums and exact rational divisions. Continuous
probability, general product measures, Fubini/Tonelli, Lebesgue integration,
convergence theorems, and statistical inference are outside this proof claim.
