# End To End: Finite Hitting Times

This lesson follows one finite hitting-time resource from an absorbing Markov
chain to first-hit probabilities, survival mass, absorption equations, and
expected hitting-time equations. It uses
[finite-hitting-times-v0](../../../artifacts/examples/math/finite-hitting-times-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_counting`, `curriculum_rationals`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_probability_theory`,
  `field_differential_equations_and_dynamical_systems`,
  `field_linear_algebra`, `field_statistics`, `field_measure_theory`, and
  `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `first-hit-distribution-witness` | `sat` | replay-only |
| `absorption-probability-equations` | `sat` | replay-only |
| `expected-hitting-time-equations` | `sat` | replay-only |
| `bad-expected-time-rejected` | `unsat` | checked |
| `general-hitting-theory-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite rational arithmetic over a finite transition
matrix. The pack does not prove recurrence or transience classifications,
infinite-horizon convergence, mixing bounds, optional stopping, or potential
theory for general Markov chains.

## Replay The Absorbing Chain

The finite chain has states:

```text
start, middle, hit
```

The target set is:

```text
target = {hit}
```

The transition matrix is row-stochastic:

```text
P(start, start)  = 1/2
P(start, middle) = 1/2
P(start, hit)    = 0

P(middle, start)  = 0
P(middle, middle) = 1/2
P(middle, hit)    = 1/2

P(hit, start)  = 0
P(hit, middle) = 0
P(hit, hit)    = 1
```

The validator checks each row sums to `1` before using the table.

## Replay First-Hit Probabilities

The initial state is `start`. The checker moves only mass that has not already
hit the target.

At time `1`, no mass reaches `hit`:

```text
P(T = 1) = 0
not-hit mass after step 1: start = 1/2, middle = 1/2
```

At time `2`, only the time-1 `middle` mass can hit:

```text
P(T = 2) = (1/2)*(1/2) = 1/4
not-hit mass after step 2: start = 1/4, middle = 1/2
```

At time `3`:

```text
P(T = 3) = (1/2)*(1/2) = 1/4
not-hit mass after step 3: start = 1/8, middle = 3/8
```

At time `4`:

```text
P(T = 4) = (3/8)*(1/2) = 3/16
```

The survival mass after horizon `4` is:

```text
P(T > 4) = 5/16
```

The validator checks that the finite accounting sums to one:

```text
0 + 1/4 + 1/4 + 3/16 + 5/16 = 1
```

## Replay Absorption Probabilities

The listed absorption probabilities are:

```text
p(start) = 1
p(middle) = 1
p(hit) = 1
```

The checker verifies the target equation:

```text
p(hit) = 1
```

and the non-target fixed-point equations:

```text
p(start) = (1/2)*p(start) + (1/2)*p(middle)
         = (1/2)*1 + (1/2)*1
         = 1

p(middle) = (1/2)*p(middle) + (1/2)*p(hit)
          = (1/2)*1 + (1/2)*1
          = 1
```

This is a finite linear fixed-point replay, not a proof of general recurrence.

## Replay Expected Hitting Times

The listed expected hitting times are:

```text
h(hit) = 0
h(middle) = 2
h(start) = 4
```

The checker verifies the target equation:

```text
h(hit) = 0
```

and the non-target equations:

```text
h(start) = 1 + (1/2)*h(start) + (1/2)*h(middle)
         = 1 + (1/2)*4 + (1/2)*2
         = 4

h(middle) = 1 + (1/2)*h(middle) + (1/2)*h(hit)
          = 1 + (1/2)*2 + (1/2)*0
          = 2
```

The expected-time row is replay-only evidence that this finite table satisfies
the exact rational equations.

## Reject A False Expected-Time Table

The negative row claims:

```text
h(start) = 3
h(middle) = 2
h(hit) = 0
```

The checker recomputes the right-hand side of the `start` equation:

```text
1 + (1/2)*3 + (1/2)*2 = 7/2
```

and rejects the table because:

```text
7/2 != 3
```

The candidate expected-time table is untrusted; the small checker rebuilds the
finite linear equation from the transition row and target set.

The resource regression clears denominators and checks the final contradiction
as `QF_LRA`:

```text
h_start = 3
h_middle = 2
2*h_start = 2 + h_start + h_middle
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Name The Lean Horizon

The finite pack checks:

```text
finite row-stochastic transition matrices
finite target sets
bounded first-hit distributions
survival mass after a finite horizon
absorption-probability fixed-point equations
expected hitting-time linear equations
bad expected-time-table refutations
```

The following remain proof-assistant targets:

```text
recurrence and transience classifications
infinite-horizon hitting probabilities
optional stopping
mixing bounds
Markov-chain potential theory
```

Those stay Lean-horizon until no-sorry probability and Markov-chain artifacts
exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite hitting-time resource pattern:

```text
untrusted fast search -> transition matrix, hitting distribution, potential table, or counterexample row
trusted small checking -> exact rational finite transition and linear-equation replay
remaining horizon -> general hitting-time and Markov-chain potential theory
```

The graduation target is to encode finite hitting events and absorbing targets
over explicit finite transition matrices, replay first-hit distributions,
survival probabilities, absorption probabilities, and expected hitting-time
equations by exact rational arithmetic, and emit checked counterexample
evidence for malformed potential or hitting-time tables.
