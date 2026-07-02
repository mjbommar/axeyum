# Concentration Theorem Boundary

This page separates the finite concentration resources Axeyum can check today
from the general probability, statistics, and asymptotic theorems that still
need a kernel-checked theorem route. It is a boundary map, not a new proof
route.

Primary pack:

- [finite-concentration-v0](../../../artifacts/examples/math/finite-concentration-v0/)

Concept rows:

- `bridge_probability_mass_table`
- `bridge_tail_count_obstruction`
- `field_probability_theory`
- `field_statistics`
- `field_measure_theory`
- `field_real_analysis`
- `field_set_theory_and_foundations`

## What Is Checked Today

The current concentration resource is an exact finite rational check over
explicit atom tables:

| Resource | Checked finite shadow | Trusted route |
|---|---|---|
| Markov witness | `P(X >= 2) = 1/4` and `E[X] / 2 = 1/2` on a two-atom table | exact replay |
| Chebyshev witness | centered three-point variable with `Var(Y)=2` and tail probability `1/2` | exact replay |
| Union-bound witness | four-atom events with `P(A union B)=3/4 <= P(A)+P(B)=1` | exact replay |
| Bad tail-bound row | replay computes `P(X >= 2)=1/4` while the claim says `<= 1/8` | exact replay plus checked QF_LRA/Farkas row |
| Bad union-bound row | replay computes `P(A union B)=3/4` while the claim says `<= 1/2` | exact replay plus checked QF_LRA/Farkas row |

The pack also records the theorem boundary row:

```text
general-concentration-lean-horizon
```

That row has `expected_result = not-run` and
`proof_status = lean-horizon`. It is not theorem evidence; it is a warning
label and a future work item.

## Why The Finite Rows Matter

The finite rows make tail events concrete:

```text
P(low) = 3/4
P(high) = 1/4
X(low) = 0
X(high) = 4
threshold = 2
```

From that table, the small checker recomputes:

```text
E[X] = 1
P(X >= 2) = 1/4
E[X] / threshold = 1/2
```

The same pattern checks the Chebyshev and union-bound witnesses, then rejects
malformed rows by recomputing the exact probability first and checking the
isolated rational contradiction second.

That separation is the point:

```text
source table replay -> exact finite probability value
proof-object row    -> checked QF_LRA/Farkas contradiction
```

## What Is Not Proved Yet

The current resources do not prove:

- Markov's, Chebyshev's, or union-bound schemas over arbitrary probability
  spaces;
- Chernoff, Hoeffding, Bernstein, Azuma-Hoeffding, or McDiarmid inequalities;
- laws of large numbers, central limit theorems, or empirical-process bounds;
- martingale concentration or optional-stopping theorems;
- asymptotic statistical inference guarantees;
- continuous-distribution measure construction;
- numerical sampling quality, MCMC/VI guarantees, or floating-point
  statistical-library behavior.

Those claims quantify over families of random variables, independence
assumptions, sigma-algebras, limits, moment-generating functions, or asymptotic
regimes. They are outside finite SMT replay unless a future Lean artifact
states and proves the theorem with no `sorry`.

## Graduation Route

A concentration theorem should graduate only after these artifacts exist:

1. A precise Lean statement for the theorem shape, including probability-space,
   measurability, integrability, independence, boundedness, or martingale
   hypotheses as needed.
2. Links from finite atom-table packs to the theorem statement as examples,
   not proof evidence.
3. A no-`sorry` Lean proof or a kernel-checked proof object with an axiom audit.
4. A consumer label that keeps theorem evidence separate from finite replay,
   QF_LRA/Farkas certificates, statistical-library claims, and benchmark
   claims.

Until then, the right label is:

```text
finite checked shadow + Lean/theorem horizon
```

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier --text concentration --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --route Farkas --proof-status checked --text qf-lra-bad-union-bound --require-any
```

## Trust Boundary

```text
untrusted fast search -> tail event, event union, finite bound, or theorem-shaped claim
trusted small checking -> exact rational table replay plus checked QF_LRA/Farkas conflicts
remaining horizon -> general concentration, limit, martingale, and asymptotic-statistics theorems
```

For the executable finite rows, read
[End To End: Finite Concentration](finite-concentration-end-to-end.md). For the
broader probability/statistics path, read
[Probability And Statistics](probability-and-statistics.md).
