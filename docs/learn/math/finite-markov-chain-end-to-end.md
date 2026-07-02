# End To End: Finite Markov Chains

This lesson follows one finite Markov-chain resource from exact rational
transition matrices to finite-horizon evolution, stationary distributions, and
bad row/stationary-claim rejection. It uses
[finite-markov-chain-v0](../../../artifacts/examples/math/finite-markov-chain-v0/).

Concept rows:

- `curriculum_counting`, `curriculum_rationals`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_probability_theory`, `field_linear_algebra`,
  `field_differential_equations_and_dynamical_systems`, and
  `field_statistics` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `stochastic-matrix-witness` | `sat` | replay-only |
| `finite-horizon-distribution-replay` | `sat` | replay-only |
| `stationary-distribution-witness` | `sat` | replay-only |
| `bad-stochastic-row-rejected` | `unsat` | replay-only |
| `qf-lra-bad-stochastic-row` | `unsat` | checked |
| `bad-stationary-distribution-rejected` | `unsat` | replay-only |
| `qf-lra-bad-stationary-distribution` | `unsat` | checked |

Every finite replay row is exact rational arithmetic over finite matrices and
finite distributions. The checked `qf-lra-*` rows isolate the final scalar
contradictions. The pack does not prove countably infinite Markov-chain theory,
mixing-time bounds, convergence theorems, or stochastic-process limit theorems.

## Replay A Row-Stochastic Matrix

The first witness is a three-state absorbing chain with states:

```text
start, middle, absorbed
```

The transition matrix is row-major:

```text
P(start, start)    = 1/2
P(start, middle)   = 1/2
P(start, absorbed) = 0

P(middle, start)    = 0
P(middle, middle)   = 1/2
P(middle, absorbed) = 1/2

P(absorbed, start)    = 0
P(absorbed, middle)   = 0
P(absorbed, absorbed) = 1
```

The validator checks nonnegativity and exact row sums:

```text
1/2 + 1/2 + 0 = 1
0 + 1/2 + 1/2 = 1
0 + 0 + 1 = 1
```

That is the stochastic-matrix witness.

## Replay Finite-Horizon Evolution

The initial distribution is concentrated at `start`:

```text
v0 = [1, 0, 0]
```

The validator applies exact row-vector transition multiplication. After one
step:

```text
v1 = v0 * P
   = [1/2, 1/2, 0]
```

After two steps:

```text
v2(start)    = (1/2)*(1/2) + (1/2)*0 + 0*0 = 1/4
v2(middle)   = (1/2)*(1/2) + (1/2)*(1/2) + 0*0 = 1/2
v2(absorbed) = (1/2)*0 + (1/2)*(1/2) + 0*1 = 1/4
```

So the two-step distribution is:

```text
v2 = [1/4, 1/2, 1/4]
```

The fixed-horizon absorption probability after two steps is therefore:

```text
P(absorbed after 2 steps) = 1/4
```

## Replay A Stationary Distribution

The stationary witness uses a two-state chain:

```text
P(a, a) = 1/2
P(a, b) = 1/2
P(b, a) = 1/4
P(b, b) = 3/4
```

The proposed stationary distribution is:

```text
pi = [1/3, 2/3]
```

The checker first verifies normalization:

```text
1/3 + 2/3 = 1
```

Then it recomputes `pi * P`:

```text
(pi * P)(a) = (1/3)*(1/2) + (2/3)*(1/4)
             = 1/6 + 1/6
             = 1/3

(pi * P)(b) = (1/3)*(1/2) + (2/3)*(3/4)
             = 1/6 + 1/2
             = 2/3
```

The row is accepted because:

```text
pi * P = pi
```

This is finite replay, not a proof of convergence to stationarity.

## Reject A Bad Transition Row

The negative row uses this malformed transition matrix:

```text
bad P = [[1/2, 1/2],
         [1/3, 1/3]]
```

The checker recomputes the row sums:

```text
row 0: 1/2 + 1/2 = 1
row 1: 1/3 + 1/3 = 2/3
```

and rejects the matrix because:

```text
2/3 != 1
```

The candidate transition matrix is untrusted; the small checker rebuilds row
sums and finite matrix products directly from the rational entries. The
separate checked `qf-lra-bad-stochastic-row` row isolates the final row-sum
contradiction as `QF_LRA`:

```text
p10 = 1/3
p11 = 1/3
row_sum = p10 + p11
row_sum = 1
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Reject A Bad Stationary Distribution

The second bad row reuses the valid two-state chain but proposes:

```text
pi_bad = [1/2, 1/2]
```

The checker recomputes:

```text
(pi_bad * P)(a) = (1/2)*(1/2) + (1/2)*(1/4)
                = 1/4 + 1/8
                = 3/8

(pi_bad * P)(b) = (1/2)*(1/2) + (1/2)*(3/4)
                = 1/4 + 3/8
                = 5/8
```

So:

```text
pi_bad * P = [3/8, 5/8] != [1/2, 1/2]
```

The separate checked `qf-lra-bad-stationary-distribution` row isolates the
first-coordinate contradiction as `QF_LRA`:

```text
8 * pi_next_a = 3
pi_next_a = 1/2
```

That keeps the trust boundary small: matrix evolution is replayed from the
source rational table, then the final false stationary equality is checked with
Farkas evidence.

## Name The Lean Horizon

The finite pack checks:

```text
finite transition matrices
row-stochasticity
finite distributions
fixed-horizon distribution replay
fixed-horizon absorption probability
stationary distribution replay
replayed bad transition-row and stationary-distribution rejections
separate checked QF_LRA/Farkas scalar refutations
```

The following remain proof-assistant targets:

```text
countably infinite Markov chains
mixing-time bounds
convergence theorems
stochastic-process limit theorems
```

Those stay Lean-horizon until no-sorry Markov-chain and stochastic-process
artifacts exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_markov_chain_bad_stochastic_row_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_markov_chain_bad_stationary_distribution_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite Markov-chain resource pattern:

```text
untrusted fast search -> transition matrix, distribution, stationary claim, or counterexample row
trusted small checking -> exact rational row sums, finite matrix products, and Farkas certificates for linear refutations
remaining horizon -> general Markov-chain convergence and mixing theory
```

The graduation target is to encode stochastic-matrix and finite-horizon
distribution checks as deterministic rational obligations, replay transition
matrices, distributions, and stationary witnesses through exact rational matrix
evaluation, and keep broader convergence and mixing claims under explicit
Lean/proof-horizon metadata.
