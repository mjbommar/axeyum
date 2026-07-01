# End To End: Finite Stochastic Kernels

This lesson follows one finite stochastic-kernel resource from row-normalized
conditional probability tables to pushforward distributions, disintegration,
and kernel composition. It uses
[finite-stochastic-kernels-v0](../../../artifacts/examples/math/finite-stochastic-kernels-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_rationals`, `curriculum_counting`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_probability_theory`, `field_measure_theory`, `field_statistics`,
  `field_linear_algebra`, `field_differential_equations_and_dynamical_systems`,
  and `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `kernel-normalization-witness` | `sat` | replay-only |
| `kernel-pushforward-witness` | `sat` | replay-only |
| `joint-disintegration-witness` | `sat` | replay-only |
| `kernel-composition-witness` | `sat` | replay-only |
| `bad-kernel-row-rejected` | `unsat` | checked |
| `general-kernel-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite rational arithmetic over labeled finite
source and target sets. The pack does not prove regular conditional
probabilities, disintegration theorems, Markov kernels on arbitrary measurable
spaces, or stochastic-process convergence.

## Replay A Kernel Table

The base kernel maps weather states to commute choices:

```text
source = sunny, rainy
target = walk, bus

K(sunny, walk) = 3/4
K(sunny, bus)  = 1/4
K(rainy, walk) = 1/5
K(rainy, bus)  = 4/5
```

The validator checks every source row is a probability distribution:

```text
K(sunny, walk) + K(sunny, bus) = 3/4 + 1/4 = 1
K(rainy, walk) + K(rainy, bus) = 1/5 + 4/5 = 1
```

That row-normalization check is the finite kernel witness.

## Replay Pushforward Through The Kernel

The source distribution is:

```text
mu(sunny) = 2/3
mu(rainy) = 1/3
```

The checker recomputes the target distribution by exact finite sums:

```text
nu(walk) = mu(sunny)*K(sunny, walk) + mu(rainy)*K(rainy, walk)
         = (2/3)*(3/4) + (1/3)*(1/5)
         = 17/30

nu(bus) = mu(sunny)*K(sunny, bus) + mu(rainy)*K(rainy, bus)
        = (2/3)*(1/4) + (1/3)*(4/5)
        = 13/30
```

The pushed-forward distribution is accepted because the recomputed values match
the witness table.

## Replay Joint Factorization And Disintegration

The joint table induced by `mu` and `K` is:

```text
P_joint(sunny, walk) = (2/3)*(3/4) = 1/2
P_joint(sunny, bus)  = (2/3)*(1/4) = 1/6
P_joint(rainy, walk) = (1/3)*(1/5) = 1/15
P_joint(rainy, bus)  = (1/3)*(4/5) = 4/15
```

The checker marginalizes the target side:

```text
P_target(walk) = 1/2 + 1/15 = 17/30
P_target(bus)  = 1/6 + 4/15 = 13/30
```

It also recovers the kernel rows by exact finite division:

```text
K(sunny, walk) = P_joint(sunny, walk) / mu(sunny)
               = (1/2) / (2/3)
               = 3/4

K(rainy, bus) = P_joint(rainy, bus) / mu(rainy)
              = (4/15) / (1/3)
              = 4/5
```

This is the finite-table shadow of disintegration.

## Replay Kernel Composition

A second kernel maps commute choices to arrival states:

```text
L(walk, early) = 2/3
L(walk, late)  = 1/3
L(bus, early)  = 1/5
L(bus, late)   = 4/5
```

The composed kernel sums over the middle commute choice:

```text
KL(sunny, early) = K(sunny, walk)*L(walk, early)
                 + K(sunny, bus)*L(bus, early)
                 = (3/4)*(2/3) + (1/4)*(1/5)
                 = 11/20

KL(sunny, late) = (3/4)*(1/3) + (1/4)*(4/5)
                = 9/20

KL(rainy, early) = (1/5)*(2/3) + (4/5)*(1/5)
                 = 22/75

KL(rainy, late) = (1/5)*(1/3) + (4/5)*(4/5)
                = 53/75
```

The composition row is replay-only evidence that the finite matrix-style
kernel product matches the listed table.

## Reject A Malformed Kernel Row

The negative row changes the rainy source row:

```text
bad K(rainy, walk) = 3/5
bad K(rainy, bus)  = 3/5
```

The checker recomputes the row sum:

```text
3/5 + 3/5 = 6/5
```

and rejects the row because:

```text
6/5 != 1
```

The candidate kernel is untrusted; the small checker rebuilds row sums and
finite pushforward/factorization equations from the listed rational table.

## Name The Lean Horizon

The finite pack checks:

```text
finite source and target sets
row-normalized rational kernel tables
pushforward distributions through kernels
joint-table factorization
kernel recovery by finite disintegration
finite kernel composition
bad kernel-row and bad composition-entry refutations
```

The following remain proof-assistant targets:

```text
regular conditional probabilities
disintegration theorems
measurable Markov kernels
stochastic-process convergence
```

Those stay Lean-horizon until no-sorry probability and measure-theory artifacts
exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-stochastic-kernels-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite stochastic-kernel resource pattern:

```text
untrusted fast search -> kernel, pushforward, joint table, composition, or counterexample row
trusted small checking -> exact rational row sums, products, quotients, and finite sums
remaining horizon -> general Markov-kernel and disintegration theory
```

The graduation target is to encode finite kernels as labeled source-to-target
probability tables, replay normalization, pushforward, joint factorization,
disintegration, and composition by exact rational sums, and emit checked
counterexample evidence for malformed kernel rows.
