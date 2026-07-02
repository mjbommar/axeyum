# Random Variable Theorem Boundary

This page is a trust-boundary note for learners, proof contributors, solver
contributors, and downstream consumers. It explains what Axeyum's finite
random-variable resource checks today, and what remains a theorem-prover
horizon.

Primary pack:

- [finite-random-variables-v0](../../../artifacts/examples/math/finite-random-variables-v0/)

Companion lessons and maps:

- [End To End: Finite Random Variables](finite-random-variables-end-to-end.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack works over finite probability tables and total finite functions from
source atoms to outcome labels. The main weather/commute witness is:

```text
P(clear) = 1/2
P(rain)  = 1/4
P(storm) = 1/4

X(clear) = short
X(rain)  = medium
X(storm) = long
```

The validator recomputes the pushforward distribution:

```text
P(X = short)  = 1/2
P(X = medium) = 1/4
P(X = long)   = 1/4
```

It also recomputes the expectation from source atoms and from the pushforward
distribution:

```text
10*(1/2) + 20*(1/4) + 40*(1/4) = 20
```

A second four-atom table checks finite independence by recomputing marginals
and every joint mass.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `pushforward-distribution-witness` | `sat` | replay-only | The finite function pushes source mass to `short:1/2`, `medium:1/4`, `long:1/4`. |
| `expectation-through-pushforward-witness` | `sat` | replay-only | Source-atom and pushforward expectation both compute `20`. |
| `independent-random-variables-witness` | `sat` | replay-only | A finite four-atom product table satisfies the independence equations. |
| `bad-pushforward-rejected` | `unsat` | replay-only | Exact replay rejects the false claim `P(X = long) = 1/2`. |
| `qf-lra-bad-pushforward` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated scalar pushforward contradiction. |
| `bad-expectation-through-pushforward-rejected` | `unsat` | replay-only | Exact replay rejects the false claim `E[X] = 25`. |
| `qf-lra-bad-expectation-through-pushforward` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated expectation contradiction. |
| `general-random-variable-lean-horizon` | `not-run` | lean-horizon | General measurable random-variable theory remains future Lean work. |

The checked rows are finite scalar contradictions after replay has recomputed
the mathematical quantities. They are not proofs of measurable-function,
distribution-law, or continuous-random-variable theorems.

## What Is Not Proved Yet

The following stay out of the checked finite resource:

- general measurable-function definitions over arbitrary measurable spaces;
- distribution laws beyond committed finite pushforward tables;
- expectation, integration, and almost-everywhere facts over general measure
  spaces;
- independence theorems for arbitrary families of random variables;
- conditional expectation, stochastic kernels, martingales, and stopping-time
  theory;
- continuous random variables and density calculus;
- convergence in probability, almost-sure convergence, laws of large numbers,
  CLT, and distributional convergence;
- simulation, floating-point, sampling-quality, or statistical-inference
  guarantees.

Those require theorem statements with explicit hypotheses and no-`sorry` Lean
proofs before they can graduate from horizon rows.

## Query The Boundary

Find random-variable theorem-horizon rows and the finite shadows beside them:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text random-variable \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-random-variables-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-random-variables-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked scalar contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-random-variables-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-pushforward \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-random-variables-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-expectation-through-pushforward \
  --require-any
```

## Graduation Criteria

General random-variable resources graduate only when they add:

1. precise Lean theorem statements for measurable random variables,
   pushforwards, expectations, distribution laws, or convergence modes;
2. explicit measurable-space, sigma-algebra, integrability, independence,
   finite-family, or convergence hypotheses;
3. no-`sorry` proofs with an axiom audit;
4. finite packs retained only as examples and regression seeds;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, the finite random-variable rows remain bounded/computable
resources:

```text
untrusted fast search -> candidate random variable, distribution, expectation, or independence row
trusted small checking -> exact finite functions, rational atom sums, and Farkas evidence
theorem horizon       -> general measurable random-variable and convergence theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text random-variable --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --proof-status lean-horizon --require-any
```

Expected resource boundary: the finite pack validates, the `horizon-frontier`
query shows `checked-finite-shadow`, and the general theorem row remains
`lean-horizon`.
