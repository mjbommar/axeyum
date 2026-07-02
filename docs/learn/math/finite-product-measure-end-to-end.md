# End To End: Finite Product Measure

This lesson follows one finite product-measure resource from factor probability
tables to rectangle probabilities, marginals, and finite Fubini replay. It uses
[finite-product-measure-v0](../../../artifacts/examples/math/finite-product-measure-v0/).
For the focused finite/general theorem boundary, read
[Fubini Tonelli Theorem Boundary](fubini-tonelli-theorem-boundary.md).

Concept rows:

- `curriculum_sets`, `curriculum_rationals`, and `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_measure_theory`, `field_probability_theory`, `field_statistics`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `product-measure-table-witness` | `sat` | replay-only |
| `marginalization-witness` | `sat` | replay-only |
| `finite-fubini-witness` | `sat` | replay-only |
| `bad-product-measure-rejected` | `unsat` | checked |
| `bad-product-marginal-rejected` | `unsat` | checked |
| `fubini-tonelli-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite rational arithmetic over normalized factor
probability tables. The pack does not prove general product-measure
construction, Fubini/Tonelli, kernels, stochastic processes, or
almost-everywhere reasoning.

## Replay The Product Table

The factor spaces are a fair coin and a fair three-sided die:

```text
P(heads) = 1/2
P(tails) = 1/2

Q(one) = 1/3
Q(two) = 1/3
Q(three) = 1/3
```

The validator checks that the product table contains exactly the Cartesian
product atoms and that every product probability is the factor product:

```text
R(heads, one)   = (1/2) * (1/3) = 1/6
R(heads, two)   = (1/2) * (1/3) = 1/6
R(heads, three) = (1/2) * (1/3) = 1/6
R(tails, one)   = (1/2) * (1/3) = 1/6
R(tails, two)   = (1/2) * (1/3) = 1/6
R(tails, three) = (1/2) * (1/3) = 1/6
```

This is the finite table version of forming a product measure.

## Replay A Rectangle Probability

The rectangle event is:

```text
{heads} x {two, three}
```

The checker recomputes it two ways. From the factor measures:

```text
P({heads}) * Q({two, three}) = (1/2) * (2/3) = 1/3
```

From the product table:

```text
R(heads, two) + R(heads, three) = 1/6 + 1/6 = 1/3
```

Both routes must agree.

## Replay The Marginals

The product table should recover the original factors when summed along each
axis. The checker recomputes the left marginal:

```text
sum_y R(heads, y) = 1/6 + 1/6 + 1/6 = 1/2
sum_y R(tails, y) = 1/6 + 1/6 + 1/6 = 1/2
```

and the right marginal:

```text
sum_x R(x, one)   = 1/6 + 1/6 = 1/3
sum_x R(x, two)   = 1/6 + 1/6 = 1/3
sum_x R(x, three) = 1/6 + 1/6 = 1/3
```

This catches product tables that have the right total mass but wrong row or
column sums.

## Replay Finite Fubini

The simple function on the product atoms is:

```text
f(heads, one)   = 1
f(heads, two)   = 2
f(heads, three) = 3
f(tails, one)   = 2
f(tails, two)   = 4
f(tails, three) = 6
```

The direct finite integral is:

```text
sum_(x,y) f(x,y) R(x,y)
  = (1 + 2 + 3 + 2 + 4 + 6) * (1/6)
  = 18/6
  = 3
```

The left-then-right iterated sum is:

```text
sum_y f(heads, y) Q(y) = (1 + 2 + 3) * (1/3) = 2
sum_y f(tails, y) Q(y) = (2 + 4 + 6) * (1/3) = 4

sum_x P(x) * sum_y f(x,y) Q(y) = (1/2)*2 + (1/2)*4 = 3
```

The right-then-left iterated sum is:

```text
sum_x f(x, one) P(x)   = (1 + 2) * (1/2) = 3/2
sum_x f(x, two) P(x)   = (2 + 4) * (1/2) = 3
sum_x f(x, three) P(x) = (3 + 6) * (1/2) = 9/2

sum_y Q(y) * sum_x f(x,y) P(x)
  = (1/3)*(3/2) + (1/3)*3 + (1/3)*(9/2)
  = 3
```

The finite Fubini row is replay-only evidence that all three exact finite sums
match on this table.

## Reject A False Product Probability

The negative row claims:

```text
R(heads, one) = 1/5
```

The checker recomputes the factor product:

```text
P(heads) * Q(one) = (1/2) * (1/3) = 1/6
```

and rejects the claim because:

```text
1/6 != 1/5
```

The candidate product probability is untrusted; the small checker multiplies
the factor probabilities directly.

## Reject A False Marginal

The second negative row claims:

```text
sum_y R(heads, y) = 2/3
```

The checker recomputes the row sum from the product table:

```text
R(heads, one) + R(heads, two) + R(heads, three)
  = 1/6 + 1/6 + 1/6
  = 1/2
```

and rejects the claim because:

```text
1/2 != 2/3
```

The product table is untrusted; the small checker independently sums the row
before the QF_LRA/Farkas artifact checks only the final scalar conflict.

## Name The Lean Horizon

The finite pack checks:

```text
normalized finite factor probabilities
Cartesian-product probability tables
rectangle probabilities
left and right marginals
finite direct and iterated sums
bad product-probability refutations
bad marginal refutations
```

The following remain proof-assistant targets:

```text
general product-measure construction
Fubini/Tonelli
measurably indexed kernels
stochastic processes
almost-everywhere equivalence for product integrals
```

Those stay Lean-horizon until no-sorry measure-theory artifacts exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

Route regression:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes finite_product_measure_bad_marginal_artifact_emits_checked_farkas
```

## Trust Boundary

This lesson shows Axeyum's current finite product-measure resource pattern:

```text
untrusted fast search -> product table, marginal, Fubini, or counterexample row
trusted small checking -> exact rational finite sums and factor products
remaining horizon -> general product-measure and Fubini/Tonelli theory
```

The graduation target is to encode finite product measures as exact rational
Cartesian-product probability tables, replay finite rectangle, marginalization,
and iterated-integral witnesses through Axeyum model evaluation, and emit
checked counterexample evidence for rejected product-probability and marginal
claims.
