# Stochastic Kernel Theorem Boundary

This page separates Axeyum's finite stochastic-kernel resource from general
regular conditional probability, disintegration, measurable Markov-kernel, and
stochastic-process theorem claims.

Primary pack:

- [finite-stochastic-kernels-v0](../../../artifacts/examples/math/finite-stochastic-kernels-v0/)

Companion lessons and maps:

- [End To End: Finite Stochastic Kernels](finite-stochastic-kernels-end-to-end.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack works over finite source and target sets. A kernel is a table that
assigns a normalized target distribution to each source point:

```text
source = sunny, rainy
target = walk, bus

K(sunny, walk) = 3/4
K(sunny, bus)  = 1/4
K(rainy, walk) = 1/5
K(rainy, bus)  = 4/5
```

The validator checks each row exactly:

```text
K(sunny, walk) + K(sunny, bus) = 1
K(rainy, walk) + K(rainy, bus) = 1
```

It then pushes a finite source distribution through the kernel:

```text
mu(sunny) = 2/3
mu(rainy) = 1/3

nu(walk) = 2/3*3/4 + 1/3*1/5 = 17/30
nu(bus)  = 2/3*1/4 + 1/3*4/5 = 13/30
```

The same pack also replays a finite joint-table factorization,
disintegration back to conditional rows, and a two-step kernel composition
through commute choice into an arrival state. In that composition the rainy to
early entry is:

```text
1/5*2/3 + 4/5*1/5 = 22/75
```

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `kernel-normalization-witness` | `sat` | replay-only | Every source row is a normalized finite probability distribution. |
| `kernel-pushforward-witness` | `sat` | replay-only | The finite source distribution pushes forward to `walk:17/30`, `bus:13/30`. |
| `joint-disintegration-witness` | `sat` | replay-only | The joint table factors through the source distribution and recovers the finite kernel rows. |
| `kernel-composition-witness` | `sat` | replay-only | The listed weather-to-arrival table is the exact composition of two finite kernels. |
| `bad-kernel-row-rejected` | `unsat` | replay-only | Exact replay rejects a malformed rainy row with sum `6/5`. |
| `qf-lra-bad-kernel-row` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated scalar contradiction `6/5 = 1`. |
| `bad-kernel-composition-rejected` | `unsat` | replay-only | Exact replay rejects the false rainy-to-early claim `1/3`; the value is `22/75`. |
| `qf-lra-bad-kernel-composition` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated composed-entry contradiction. |
| `general-kernel-lean-horizon` | `not-run` | lean-horizon | General stochastic-kernel theory remains future proof-assistant work. |

The checked rows are finite scalar contradictions after exact replay has
computed the source quantities. They are not proofs of general disintegration,
regular conditional probability, Markov-process, or stochastic calculus
theorems.

## What Is Not Proved Yet

The current pack does not prove:

- regular conditional probabilities over arbitrary measurable spaces;
- disintegration theorems beyond the displayed finite joint tables;
- measurable Markov kernels or kernel measurability conditions;
- kernels on countable, standard Borel, or continuous state spaces;
- transition semigroups, Feller properties, ergodicity, or mixing theorems;
- stochastic-process convergence, martingale-process, or SDE results;
- simulation, sampling, MCMC, floating-point, or statistical-library
  guarantees.

Those claims require theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows.

## Query The Boundary

Find stochastic-kernel theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text stochastic-kernel \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked scalar contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-kernel-row \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-kernel-composition \
  --require-any
```

## Graduation Criteria

General stochastic-kernel resources graduate only when they add:

1. precise Lean theorem statements for regular conditional probabilities,
   disintegration, measurable Markov kernels, or process convergence;
2. explicit measurable-space, sigma-algebra, standard-Borel, integrability,
   kernel-measurability, and finite/countable/continuous-state hypotheses;
3. no-`sorry` proofs with an axiom audit;
4. finite kernel packs retained as examples and regression seeds;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, the finite stochastic-kernel rows remain bounded/computable
resources:

```text
untrusted fast search -> candidate finite kernel, joint table, composition, or malformed claim
trusted small checking -> exact rational row sums, pushforwards, composition replay, and Farkas evidence
theorem horizon       -> regular conditional probability, disintegration, and measurable Markov kernels
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-stochastic-kernels-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text stochastic-kernel --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the general theorem
row remains `lean-horizon`.
