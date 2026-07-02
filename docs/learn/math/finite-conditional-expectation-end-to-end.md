# End To End: Finite Conditional Expectation

This lesson follows one finite conditional-expectation resource from atom
probabilities to block averages, total expectation, tower-property replay, and
conditional variance decomposition. It uses
[finite-conditional-expectation-v0](../../../artifacts/examples/math/finite-conditional-expectation-v0/).
For the focused finite-versus-theorem boundary, read
[Conditional Expectation Theorem Boundary](conditional-expectation-theorem-boundary.md).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_rationals`, and `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_probability_theory`, `field_statistics`, `field_measure_theory`,
  `field_real_analysis`, and `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `conditional-expectation-partition-witness` | `sat` | replay-only |
| `law-total-expectation-witness` | `sat` | replay-only |
| `bad-total-expectation-rejected` | `unsat` | checked |
| `tower-property-witness` | `sat` | replay-only |
| `bad-conditional-expectation-rejected` | `unsat` | checked |
| `bad-tower-property-rejected` | `unsat` | checked |
| `conditional-variance-decomposition-witness` | `sat` | replay-only |
| `bad-variance-decomposition-rejected` | `unsat` | checked |
| `general-conditional-expectation-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite rational arithmetic over normalized atom
tables and finite partitions. The pack does not prove the Radon-Nikodym
construction, general conditional expectation, martingales, stopping-time
theorems, or regular conditional probabilities.

## Replay The Probability Space

The finite probability space has four equally likely atoms:

```text
P(a) = 1/4
P(b) = 1/4
P(c) = 1/4
P(d) = 1/4
```

The random variable is:

```text
X(a) = 0
X(b) = 2
X(c) = 4
X(d) = 8
```

The checker treats the conditioning sigma-algebra as a finite partition of the
atom set.

## Replay Blockwise Conditional Expectation

The conditioning partition is:

```text
low  = {a,b}
high = {c,d}
```

The validator first checks that the blocks are nonempty, disjoint, and cover all
atoms. It then recomputes the block probabilities:

```text
P(low)  = P(a) + P(b) = 1/2
P(high) = P(c) + P(d) = 1/2
```

The low-block conditional expectation is:

```text
E[X | low]
  = (0*(1/4) + 2*(1/4)) / (1/2)
  = (1/2) / (1/2)
  = 1
```

The high-block conditional expectation is:

```text
E[X | high]
  = (4*(1/4) + 8*(1/4)) / (1/2)
  = 3 / (1/2)
  = 6
```

So the conditional-expectation table is constant on each block:

```text
CE_partition(a) = 1
CE_partition(b) = 1
CE_partition(c) = 6
CE_partition(d) = 6
```

## Replay Total Expectation

The original expectation is:

```text
E[X] = 0*(1/4) + 2*(1/4) + 4*(1/4) + 8*(1/4)
     = 7/2
```

The expectation of the conditional expectation is:

```text
E[E[X | partition]] = 1*(1/2) + 6*(1/2)
                    = 7/2
```

The law-of-total-expectation row is replay-only evidence that these exact
rational sums agree on the finite table.

## Reject A False Total Expectation

The negative total-expectation row keeps the same atom table, random variable,
partition, and conditional-expectation table, but claims:

```text
claimed E[E[X | partition]] = 4
```

The checker recomputes:

```text
E[X]                  = 7/2
E[E[X | partition]]   = 7/2
```

and rejects the claim because:

```text
7/2 != 4
```

The source artifact is
[`bad-total-expectation-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-total-expectation-farkas-conflict.smt2).
It checks the final scalar contradiction as `QF_LRA`:

```text
conditional_expectation_expectation = source_expectation
source_expectation = 7/2
conditional_expectation_expectation = 4
```

That `unsat` result must carry checked `Evidence::UnsatFarkas`.

## Replay The Tower Property

The tower witness uses the same two-block partition as the fine partition:

```text
G = {a,b}, {c,d}
```

and the one-block partition as the coarse partition:

```text
H = {a,b,c,d}
```

The checker verifies that `G` refines `H`, then recomputes both sides:

```text
E[E[X | G] | H] = 7/2
E[X | H]        = 7/2
```

The finite tower-property row is accepted because every atom receives the same
exact rational value on both sides:

```text
a, b, c, d -> 7/2
```

## Reject A False Conditional Expectation

The negative row claims that the high block has conditional expectation `5`:

```text
claimed E[X | high] = 5
```

The checker recomputes:

```text
actual E[X | high]
  = (4*(1/4) + 8*(1/4)) / (1/2)
  = 6
```

and rejects the claim because:

```text
6 != 5
```

The resource regression checks the denominator-cleared contradiction as
`QF_LRA`:

```text
(1/2)*high_block_expectation = 3
high_block_expectation = 5
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

The candidate conditional-expectation table is untrusted; the small checker
rebuilds it from the atom probabilities, random-variable values, and partition,
then checks the small Farkas certificate for the final linear refutation.

## Reject A False Tower Value

The second negative row claims that the coarse-block value of
`E[E[X | G] | H]` is `4`:

```text
claimed E[E[X | G] | H] = 4
```

The checker recomputes the fine table:

```text
CE_G(a) = 1
CE_G(b) = 1
CE_G(c) = 6
CE_G(d) = 6
```

Then it conditions that fine table on the one-block coarse partition:

```text
E[E[X | G] | H]
  = 1*(1/4) + 1*(1/4) + 6*(1/4) + 6*(1/4)
  = 7/2
```

and rejects the claim because:

```text
7/2 != 4
```

The resource regression checks the scalar contradiction as `QF_LRA`:

```text
tower_value = 7/2
tower_value = 4
```

That `unsat` result must also carry checked `Evidence::UnsatFarkas`.

## Replay Conditional Variance Decomposition

The same finite table also checks a conditional-moment identity:

```text
E[X]   = 7/2
E[X^2] = 21
Var(X) = 21 - (7/2)^2 = 35/4
```

Within each conditioning block:

```text
Var(X | {a,b}) = ((0-1)^2 + (2-1)^2) / 2 = 1
Var(X | {c,d}) = ((4-6)^2 + (8-6)^2) / 2 = 4
```

So:

```text
E[Var(X | G)] = (1/2)*1 + (1/2)*4 = 5/2
Var(E[X | G]) = 25/4
Var(X) = E[Var(X | G)] + Var(E[X | G])
       = 5/2 + 25/4
       = 35/4
```

## Reject A False Variance Decomposition

The negative variance row keeps the same atom table, random variable,
partition, conditional-expectation table, and conditional-variance table, but
claims:

```text
claimed Var(X) = 9
```

The checker recomputes:

```text
Var(X)             = 35/4
E[Var(X | G)]      = 5/2
Var(E[X | G])      = 25/4
5/2 + 25/4         = 35/4
```

and rejects the claim because:

```text
35/4 != 9
```

The source artifact is
[`bad-variance-decomposition-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-variance-decomposition-farkas-conflict.smt2).
It checks the final scalar contradiction as `QF_LRA`:

```text
total_variance = 35/4
expected_conditional_variance = 5/2
conditional_mean_variance = 25/4
total_variance = expected_conditional_variance + conditional_mean_variance
total_variance = 9
```

That `unsat` result must carry checked `Evidence::UnsatFarkas`.

## Name The Lean Horizon

The finite pack checks:

```text
normalized finite atom probabilities
finite conditioning partitions
blockwise weighted averages
law of total expectation
nested-partition tower property
conditional variance decomposition
bad conditional-expectation-table refutations
bad total-expectation refutations
bad tower-property refutations
bad variance-decomposition refutations
```

The following remain proof-assistant targets:

```text
Radon-Nikodym construction
general conditional expectation
martingales
stopping-time theorems
regular conditional probabilities
```

Those stay Lean-horizon until no-sorry probability and measure-theory artifacts
exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conditional-expectation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_conditional_expectation_bad_variance_decomposition_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

The focused cargo regression should pass one test and filter the rest of
`math_resource_lra_routes`.

## Trust Boundary

This lesson shows Axeyum's current finite conditional-expectation resource
pattern:

```text
untrusted fast search -> partition, conditional-expectation, tower, or counterexample row
trusted small checking -> exact finite partitions, rational block averages, conditional moments, and Farkas certificates for linear refutations
remaining horizon -> general conditional-expectation theory
```

The graduation target is to encode finite conditioning sigma-algebras as
partitions of probability atoms, replay finite conditional expectations, total
expectation, tower-property, and conditional-variance witnesses by exact
rational model evaluation, and emit checked QF_LRA/Farkas evidence for
rejected conditional-expectation, total-expectation, tower-property, or
variance-decomposition tables when the final contradiction is linear.
