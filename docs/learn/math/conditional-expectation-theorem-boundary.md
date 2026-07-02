# Conditional Expectation Theorem Boundary

This page separates Axeyum's finite conditional-expectation resource from
general conditional-expectation, Radon-Nikodym, martingale, stopping-time, and
regular-conditional-probability claims.

Primary pack:

- [finite-conditional-expectation-v0](../../../artifacts/examples/math/finite-conditional-expectation-v0/)

Companion lessons and maps:

- [End To End: Finite Conditional Expectation](finite-conditional-expectation-end-to-end.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Random Variable Theorem Boundary](random-variable-theorem-boundary.md)
- [Stochastic Kernel Theorem Boundary](stochastic-kernel-theorem-boundary.md)
- [Martingale Theorem Boundary](martingale-theorem-boundary.md)
- [Lebesgue Integration Theorem Boundary](lebesgue-integration-theorem-boundary.md)

## Current Finite Resource

The pack works over a four-atom probability space:

```text
P(a) = P(b) = P(c) = P(d) = 1/4
X(a), X(b), X(c), X(d) = 0, 2, 4, 8
```

The conditioning sigma-algebra is represented as a finite partition:

```text
low  = {a,b}
high = {c,d}
```

The checker recomputes the blockwise conditional expectation exactly:

```text
E[X | low]  = (0*(1/4) + 2*(1/4)) / (1/2) = 1
E[X | high] = (4*(1/4) + 8*(1/4)) / (1/2) = 6
```

So the conditional-expectation table is:

```text
a -> 1
b -> 1
c -> 6
d -> 6
```

The pack also replays:

```text
E[X] = 7/2
E[E[X | G]] = 7/2
E[E[X | G] | H] = E[X | H] = 7/2
Var(X) = E[Var(X | G)] + Var(E[X | G]) = 35/4
```

where `G = {{a,b},{c,d}}` refines the one-block partition
`H = {{a,b,c,d}}`.

This is finite partition replay over exact rationals. It is useful probability
evidence, but it does not construct conditional expectation on arbitrary
measure spaces.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `conditional-expectation-partition-witness` | `sat` | replay-only | Exact replay recomputes the low/high block averages. |
| `law-total-expectation-witness` | `sat` | replay-only | Exact replay checks total expectation on the finite table. |
| `bad-total-expectation-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false total-expectation scalar `4`. |
| `tower-property-witness` | `sat` | replay-only | Exact replay checks the nested-partition tower identity. |
| `conditional-variance-decomposition-witness` | `sat` | replay-only | Exact replay checks finite conditional-variance decomposition. |
| `bad-conditional-expectation-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false high-block average `5`. |
| `bad-tower-property-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false tower value `4`. |
| `bad-variance-decomposition-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false variance total `9`. |
| `general-conditional-expectation-lean-horizon` | `not-run` | lean-horizon | General conditional expectation remains future proof-assistant work. |

The checked QF_LRA/Farkas rows own only the small linear contradictions after
finite replay computes the exact rational quantities. They do not certify the
existence, uniqueness, or theorem schemas for conditional expectation on
general measure spaces.

## Bad High-Block Boundary

The malformed conditional-expectation row claims:

```text
E[X | high] = 5
```

Exact replay computes:

```text
P(high) = 1/2
sum_high X * P = 4*(1/4) + 8*(1/4) = 3
E[X | high] = 3 / (1/2) = 6
```

The checked QF_LRA/Farkas artifact isolates the denominator-cleared conflict:

```text
(1/2) * high_block_expectation = 3
high_block_expectation = 5
```

This proves one fixed bad finite table impossible. It is not a general
conditional-expectation theorem.

## Total Expectation Boundary

The false total-expectation row keeps the same finite table but claims:

```text
E[E[X | G]] = 4
```

Replay computes:

```text
E[X] = 7/2
E[E[X | G]] = 1*(1/2) + 6*(1/2) = 7/2
```

The checked Farkas row certifies only that `7/2 = 4` is impossible under the
fixed replay facts.

## Tower Boundary

For nested partitions `G` and `H`, exact replay computes:

```text
E[E[X | G] | H] = 7/2
E[X | H] = 7/2
```

The malformed row claims the tower value is `4`, and the checked Farkas
artifact isolates:

```text
tower_value = 7/2
tower_value = 4
```

This is a finite nested-partition certificate. It does not prove the tower
property for arbitrary sub-sigma-algebras.

## Variance Boundary

The finite variance row recomputes:

```text
E[X] = 7/2
E[X^2] = 21
Var(X) = 35/4
E[Var(X | G)] = 5/2
Var(E[X | G]) = 25/4
```

The bad row claims:

```text
Var(X) = 9
```

The checked Farkas artifact certifies the final exact-linear contradiction for
this finite table. It does not prove general conditional-variance identities
over arbitrary probability spaces.

## What Is Not Proved Yet

The current finite conditional-expectation resource does not prove:

- existence or uniqueness of conditional expectation as a Radon-Nikodym
  derivative;
- almost-sure equality or sigma-algebra measurability theorems;
- the law of total expectation or tower property for arbitrary
  sub-sigma-algebras;
- regular conditional probabilities or disintegration theorems;
- martingale convergence, optional stopping, Doob inequalities, or
  continuous-time stochastic-process results;
- conditional distributions, conditional densities, or measure-kernel
  constructions outside finite tables;
- `L1`/`L2` projection interpretations in general Hilbert or Banach spaces.

Those claims need precise theorem statements, explicit hypotheses, no-`sorry`
Lean artifacts, and an axiom audit before they can graduate from horizon rows.

## Query The Boundary

Find the conditional-expectation horizon row and its finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-conditional-expectation-v0 \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-conditional-expectation-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite QF_LRA/Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-conditional-expectation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the separate malformed finite claims:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-conditional-expectation-v0 \
  --route Farkas \
  --proof-status checked \
  --text "high block" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-conditional-expectation-v0 \
  --route Farkas \
  --proof-status checked \
  --text "total expectation" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-conditional-expectation-v0 \
  --route Farkas \
  --proof-status checked \
  --text tower \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-conditional-expectation-v0 \
  --route Farkas \
  --proof-status checked \
  --text variance \
  --require-any
```

## Graduation Criteria

General conditional-expectation resources graduate only when they add:

1. precise Lean theorem statements for conditional expectation,
   Radon-Nikodym construction, total expectation, tower property, variance
   decomposition, regular conditional probabilities, and stopping-time links;
2. explicit hypotheses for probability spaces, sigma-algebras,
   sub-sigma-algebras, integrability, almost-sure equality, finite/infinite
   measure requirements, and measurability;
3. no-`sorry` proofs with an axiom audit;
4. links from finite partition packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, conditional-expectation rows remain bounded/computable resources:

```text
untrusted fast search -> candidate finite atom table, partition, conditional table, tower value, or variance total
trusted small checking -> exact rational partition replay plus QF_LRA/Farkas scalar evidence
theorem horizon       -> Radon-Nikodym construction, general conditional expectation, regular conditional probabilities, and stopping-time theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conditional-expectation-v0
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-conditional-expectation-v0 --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --text "total expectation" --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --text variance --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the general
conditional-expectation row remains `lean-horizon`.
