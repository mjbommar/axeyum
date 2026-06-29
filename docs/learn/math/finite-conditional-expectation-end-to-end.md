# End To End: Finite Conditional Expectation

This lesson follows one finite conditional-expectation resource from atom
probabilities to block averages, total expectation, and tower-property replay.
It uses
[finite-conditional-expectation-v0](../../../artifacts/examples/math/finite-conditional-expectation-v0/).

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
| `tower-property-witness` | `sat` | replay-only |
| `bad-conditional-expectation-rejected` | `unsat` | checked |
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

The candidate conditional-expectation table is untrusted; the small checker
rebuilds it from the atom probabilities, random-variable values, and partition.

## Name The Lean Horizon

The finite pack checks:

```text
normalized finite atom probabilities
finite conditioning partitions
blockwise weighted averages
law of total expectation
nested-partition tower property
bad conditional-expectation-table refutations
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
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite conditional-expectation resource
pattern:

```text
untrusted fast search -> partition, conditional-expectation, tower, or counterexample row
trusted small checking -> exact finite partitions and rational block averages
remaining horizon -> general conditional-expectation theory
```

The graduation target is to encode finite conditioning sigma-algebras as
partitions of probability atoms, replay finite conditional expectations, total
expectation, and tower-property witnesses by exact rational model evaluation,
and emit checked counterexample evidence for rejected conditional-expectation
tables.
