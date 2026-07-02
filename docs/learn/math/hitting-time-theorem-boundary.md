# Hitting-Time Theorem Boundary

This page separates the finite hitting-time resources Axeyum can check today
from general hitting-time, recurrence, transience, optional-stopping, mixing,
and Markov-chain potential theory.

The current resource is a concrete finite absorbing chain:

```text
states = start, middle, hit
target = {hit}
P(start,start) = 1/2    P(start,middle) = 1/2
P(middle,middle) = 1/2  P(middle,hit) = 1/2
P(hit,hit) = 1
```

Axeyum can replay the listed finite first-hit distribution, survival mass,
absorption probabilities, and expected hitting-time equations exactly over
rationals. It does not prove theorems about arbitrary Markov chains, infinite
state spaces, stopping times, or limiting behavior.

## Current Resource

Primary pack:

- [finite-hitting-times-v0](../../../artifacts/examples/math/finite-hitting-times-v0/)

Concept rows:

- `field_probability_theory`
- `field_differential_equations_and_dynamical_systems`
- `field_linear_algebra`
- `field_statistics`
- `field_measure_theory`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `curriculum_rationals`
- `curriculum_linear_algebra`

Proof routes:

- exact finite replay for transition rows, finite first-hit distributions,
  absorption probabilities, and expected hitting-time equations;
- QF_LRA/Farkas for the isolated bad survival-mass and bad expected-time
  contradictions;
- Lean horizon for general hitting-time theory.

## What Is Checked Today

| Row | What Axeyum Checks | Evidence Status |
|---|---|---|
| `first-hit-distribution-witness` | the listed `P(T=1..4)` values and `P(T>4)=5/16` by carrying only not-yet-hit mass | replay-only |
| `absorption-probability-equations` | finite fixed-point equations for absorption probabilities `p(start)=p(middle)=p(hit)=1` | replay-only |
| `expected-hitting-time-equations` | finite linear equations `h(hit)=0`, `h(middle)=2`, and `h(start)=4` | replay-only |
| `bad-survival-mass-rejected` | exact replay recomputes survival mass `5/16`, rejecting the malformed `1/4` claim | replay-only |
| `qf-lra-bad-survival-mass` | the fixed rational conflict between `survival_mass=5/16` and `survival_mass=1/4` is unsatisfiable | checked QF_LRA/Farkas |
| `bad-expected-time-rejected` | exact replay recomputes the malformed start-state equation as `7/2`, not `3` | replay-only |
| `qf-lra-bad-expected-time` | the fixed rational conflict `h_start=3`, `h_middle=2`, and `2*h_start = 2 + h_start + h_middle` is unsatisfiable | checked QF_LRA/Farkas |
| `general-hitting-theory-lean-horizon` | recurrence, transience, stopping, mixing, and potential-theory claims are explicitly future theorem work | Lean horizon |

The checked rows are small scalar contradictions that remain valid only after
finite replay computes the source values. Solver search is not trusted as
general Markov-chain theorem evidence.

## What Is Not Proved Yet

The current pack does not prove:

- recurrence or transience classifications for general Markov chains;
- infinite-horizon hitting probabilities outside the displayed finite system;
- optional stopping, stopped martingale, or stopping-time integrability
  theorems;
- mixing bounds, convergence to stationarity, or ergodic theorems;
- continuous-time Markov process or stochastic differential equation results;
- potential theory for countable or continuous state spaces;
- numerical simulation quality or floating-point stochastic-process claims.

Those claims need theorem-prover reconstruction or separate numerical-honesty
artifacts. The finite pack is an example and regression source, not a proof of
the general theory.

## Query The Boundary

From the repository root, find the theorem boundary and finite shadow:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text hitting \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked rational contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-survival-mass \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-expected-time \
  --require-any
```

## Graduation Criteria

A general hitting-time theorem resource should graduate only after these
artifacts exist:

1. Lean statements for the target theorem family: recurrence/transience,
   infinite-horizon hitting probability, optional stopping, mixing, or
   potential theory.
2. Explicit hypotheses for finite versus countable state spaces, absorbing
   targets, integrability, stopping times, and transition kernels.
3. No-`sorry` proofs with an axiom audit.
4. Links from finite hitting-time packs to theorem statements as examples and
   regression seeds, not as theorem evidence.
5. Display labels that keep finite replay, QF_LRA/Farkas contradictions, and
   theorem-level proof rows separate.

## Trust Boundary

```text
untrusted fast search -> transition table, first-hit table, potential table, or certificate
trusted small checking -> exact rational finite replay and checked QF_LRA/Farkas rows
remaining horizon -> recurrence, transience, stopping, mixing, and potential theory
```

Read this after
[End To End: Finite Hitting Times](finite-hitting-times-end-to-end.md) for the
focused finite trace, and with
[Probability And Statistics](probability-and-statistics.md) for adjacent
finite Markov-chain, martingale, kernel, and concentration resources.

## Validation

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text hitting --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --require-any
```
