# End To End: Finite Random Variables

This lesson follows one finite random-variable resource from atom probabilities
to pushforward distributions, expectations, and independence replay. It uses
[finite-random-variables-v0](../../../artifacts/examples/math/finite-random-variables-v0/).

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
| `pushforward-distribution-witness` | `sat` | replay-only |
| `expectation-through-pushforward-witness` | `sat` | replay-only |
| `independent-random-variables-witness` | `sat` | replay-only |
| `bad-pushforward-rejected` | `unsat` | checked |
| `bad-expectation-through-pushforward-rejected` | `unsat` | checked |
| `general-random-variable-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite rational arithmetic over normalized atom
tables and total finite functions. The pack does not prove general
measurable-function theory, conditional expectation, stochastic kernels,
martingales, or continuous random variables.

## Replay A Random Variable

The first finite probability space has three weather atoms:

```text
P(clear) = 1/2
P(rain) = 1/4
P(storm) = 1/4
```

The random variable is a total finite function from source atoms to outcome
labels:

```text
X(clear) = short
X(rain) = medium
X(storm) = long
```

Totality is part of the trust boundary: every source atom must have exactly one
listed image.

## Replay The Pushforward Distribution

The pushforward distribution sums source mass by outcome label:

```text
P(X = short)  = P(clear) = 1/2
P(X = medium) = P(rain) = 1/4
P(X = long)   = P(storm) = 1/4
```

The validator recomputes those masses directly from the source atom table and
the finite function graph.

## Replay Expectation Two Ways

The outcome values are:

```text
short = 10
medium = 20
long = 40
```

The source-atom expectation is:

```text
10*(1/2) + 20*(1/4) + 40*(1/4)
  = 5 + 5 + 10
  = 20
```

The pushforward expectation is:

```text
10*P(X = short) + 20*P(X = medium) + 40*P(X = long)
  = 10*(1/2) + 20*(1/4) + 40*(1/4)
  = 20
```

The checker accepts the row only because the two exact rational weighted sums
agree.

## Replay Independence

The independence witness uses a four-atom probability table:

```text
P(heads_green) = 1/4
P(heads_red)   = 1/4
P(tails_green) = 1/4
P(tails_red)   = 1/4
```

The two finite random variables are:

```text
Coin(heads_green) = heads
Coin(heads_red)   = heads
Coin(tails_green) = tails
Coin(tails_red)   = tails

Signal(heads_green) = green
Signal(heads_red)   = red
Signal(tails_green) = green
Signal(tails_red)   = red
```

The checker recomputes marginals:

```text
P(Coin = heads) = 1/2
P(Coin = tails) = 1/2
P(Signal = green) = 1/2
P(Signal = red)   = 1/2
```

and joint masses:

```text
P(Coin = heads, Signal = green) = 1/4
P(Coin = heads, Signal = red)   = 1/4
P(Coin = tails, Signal = green) = 1/4
P(Coin = tails, Signal = red)   = 1/4
```

Each joint mass equals the product of the corresponding marginals:

```text
1/4 = (1/2) * (1/2)
```

That is the finite-table independence check.

## Reject A False Pushforward Claim

The negative row claims:

```text
P(X = long) = 1/2
```

The checker recomputes the exact source mass mapped to `long`:

```text
X(storm) = long
P(storm) = 1/4
P(X = long) = 1/4
```

and rejects the claim because:

```text
1/4 != 1/2
```

The candidate distribution is untrusted; the small checker rebuilds it from the
source atom table and the finite function.

## Reject A False Expectation Claim

The second negative row claims:

```text
E[X] = 25
```

The checker recomputes expectation from the atom table:

```text
10*(1/2) + 20*(1/4) + 40*(1/4) = 20
```

and recomputes the same value from the pushforward distribution:

```text
10*P(X = short) + 20*P(X = medium) + 40*P(X = long) = 20
```

The source-linked QF_LRA artifact then isolates the checked contradiction:

```text
expectation_value = 20
expectation_value = 25
```

The untrusted row can suggest an expectation, but the checker rebuilds the
weighted sums before the Farkas route proves the final exact-linear conflict.

## Name The Lean Horizon

The finite pack checks:

```text
normalized finite atom probabilities
total finite random-variable functions
pushforward distributions
expectation from source atoms and pushforward distributions
joint and marginal distributions
finite independence
bad pushforward and bad expectation refutations
```

The following remain proof-assistant targets:

```text
general measurable functions
distribution laws for arbitrary measurable spaces
conditional expectation
stochastic kernels
martingales
continuous random variables
```

Those stay Lean-horizon until no-sorry probability and measure-theory artifacts
exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite random-variable resource pattern:

```text
untrusted fast search -> random-variable, distribution, expectation, independence, or counterexample row
trusted small checking -> exact finite functions and rational atom sums
remaining horizon -> general measurable random-variable theory
```

The graduation target is to encode finite random variables as total finite
functions from probability atoms to outcome labels, replay finite pushforward,
expectation, and independence witnesses through exact rational model
evaluation, and emit checked counterexample evidence for rejected
pushforward-distribution claims.
