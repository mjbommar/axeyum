# Dynamics Resource Consumer Queries

This guide turns the finite differential-equations and dynamical-systems rows
in the foundational-resource JSON contract into copyable downstream queries.
It is a consumer-discovery layer, not a new proof route and not a claim of
continuous ODE/PDE theorem coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite recurrence, Euler, Markov, or hitting-time rows match this proof route?
```

The current dynamics surface is finite and exact-rational: recurrence traces,
transition-step replay, bounded invariant checks, explicit Euler step and
finite error replay, stochastic-kernel rows, finite Markov-chain stochasticity
and stationary-distribution replay plus explicit QF_LRA/Farkas scalar rows,
finite hitting-time equations, and algebraic
derivative/integral shadows used as prerequisites. Existence/uniqueness,
continuous flows, stability theory, chaos, PDEs, stochastic differential
equations, and convergence guarantees remain in the proof-horizon or
numerical-honesty lanes.

## Query Shape

Start with the field summary:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field differential_equations_and_dynamical_systems \
  --route Farkas \
  --require-any
```

Then drill into bridge concepts or checked rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept <bridge_concept_id> \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept <bridge_concept_id> \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Use `packs` for a catalog row or pack path. Use `checks` when the consumer
needs concrete checked rows to display.

## Dynamics Query Families

| Family | Concept Or Pack Filter | Route Filter | Start Query |
|---|---|---|---|
| Finite recurrences, transition steps, invariants, and Euler rows | `bridge_finite_dynamics_euler_replay` | `Farkas` | `checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked` |
| Bounded family rows versus convergence/asymptotic theorem boundaries | `bridge_bounded_family_asymptotic_boundary` | `Farkas`; `LIA` | `checks --concept bridge_bounded_family_asymptotic_boundary --route Farkas --proof-status checked`; `checks --concept bridge_bounded_family_asymptotic_boundary --route LIA --proof-status checked` |
| Stochastic kernels, Markov chains, and hitting-time equations | `bridge_stochastic_kernel` | `Farkas` | `checks --concept bridge_stochastic_kernel --route Farkas --proof-status checked` |
| Bounded deterministic dynamics proof rows | pack `bounded-dynamics-v0` | `Farkas` | `checks --pack bounded-dynamics-v0 --route Farkas --proof-status checked --text qf-lra-bad-transition-step` |
| Bounded threshold-step refutations | pack `bounded-dynamics-v0` | `Farkas` | `checks --pack bounded-dynamics-v0 --route Farkas --proof-status checked --text qf-lra-bad-threshold-step` |
| Explicit Euler display rows | pack `finite-euler-method-v0` | `Farkas` | `checks --pack finite-euler-method-v0 --route Farkas --proof-status checked` |
| Finite Markov-chain display rows | pack `finite-markov-chain-v0` | `Farkas` | `checks --pack finite-markov-chain-v0 --route Farkas --proof-status checked --text qf-lra-bad-stationary-distribution` |
| Hitting-time display rows | pack `finite-hitting-times-v0` | `Farkas` | `checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --text qf-lra-bad-expected-time` |
| Calculus shadow prerequisites | packs `calculus-algebraic-shadow-v0`, `calculus-riemann-sum-v0` | `Farkas` | `checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked`; `checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked` |

## Copyable Examples

List all promoted finite dynamics packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field differential_equations_and_dynamical_systems \
  --route Farkas \
  --require-any
```

Display all checked finite dynamics rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field differential_equations_and_dynamical_systems \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display finite recurrence, transition, invariant, and Euler rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_dynamics_euler_replay \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display finite-family rows that deliberately stop before convergence,
closed-form, or asymptotic theorem claims:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field differential_equations_and_dynamical_systems \
  --text asymptotic \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_family_asymptotic_boundary \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display the focused finite affine-recurrence proof row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-affine-step \
  --require-any
```

Display stochastic-kernel, Markov-chain, and hitting-time rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_stochastic_kernel \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For focused UI cards, query individual packs:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack bounded-dynamics-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack bounded-dynamics-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-threshold-step \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-euler-method-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text ODE \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-markov-chain-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-expected-time \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text hitting \
  --require-any
```

Display calculus shadow prerequisites used by the finite dynamics lane:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack calculus-algebraic-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack calculus-riemann-sum-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked dynamics rows, not
theorem coverage. They can support a catalog, learner page, route-specific
regression search, or sibling resource that wants examples by finite dynamics
object family.

For the finite Euler boundary in particular, read
[Euler Method Theorem Boundary](../learn/math/euler-method-theorem-boundary.md)
before displaying ODE convergence, stability, stiffness, floating-point, or
PDE theorem language next to finite transition/error rows.

For the finite hitting-time boundary, read
[Hitting-Time Theorem Boundary](../learn/math/hitting-time-theorem-boundary.md)
before displaying recurrence/transience, optional stopping, mixing, potential
theory, or continuous-time Markov-process language next to finite transition
and expected-time rows.

They do not prove:

- continuous ODE existence, uniqueness, flow, stability, or bifurcation
  theorems;
- PDE theory, chaos theory, ergodic theory, or stochastic differential
  equations;
- Euler-method convergence, global truncation error, conditioning, or
  floating-point stability;
- stochastic-process limit theorems or continuous-time Markov processes;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numeric-honesty artifacts, or benchmark evidence before they can graduate.
