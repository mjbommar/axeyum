# Fubini Tonelli Theorem Boundary

This page separates Axeyum's finite product-measure resource from general
product-measure, Fubini, Tonelli, and almost-everywhere theorem claims.

Primary pack:

- [finite-product-measure-v0](../../../artifacts/examples/math/finite-product-measure-v0/)

Companion lessons and maps:

- [End To End: Finite Product Measure](finite-product-measure-end-to-end.md)
- [Lebesgue Integration Theorem Boundary](lebesgue-integration-theorem-boundary.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Random Variable Theorem Boundary](random-variable-theorem-boundary.md)
- [Stochastic Kernel Theorem Boundary](stochastic-kernel-theorem-boundary.md)

## Current Finite Resource

The pack works over two finite probability spaces: a fair coin and a fair
three-sided die.

```text
P(heads) = 1/2
P(tails) = 1/2

Q(one)   = 1/3
Q(two)   = 1/3
Q(three) = 1/3
```

The product table is a finite Cartesian product. Every atom is recomputed by
exact multiplication:

```text
R(heads, one)   = (1/2) * (1/3) = 1/6
R(heads, two)   = (1/2) * (1/3) = 1/6
R(heads, three) = (1/2) * (1/3) = 1/6
R(tails, one)   = (1/2) * (1/3) = 1/6
R(tails, two)   = (1/2) * (1/3) = 1/6
R(tails, three) = (1/2) * (1/3) = 1/6
```

The checker also recomputes a rectangle probability:

```text
R({heads} x {two, three}) = 1/6 + 1/6 = 1/3
P({heads}) * Q({two, three}) = (1/2) * (2/3) = 1/3
```

and both marginals:

```text
sum_y R(heads, y) = 1/6 + 1/6 + 1/6 = 1/2
sum_x R(x, one)   = 1/6 + 1/6 = 1/3
```

This is finite product-measure replay. It is not a construction of product
measures over arbitrary measurable spaces.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `product-measure-table-witness` | `sat` | replay-only | The displayed finite Cartesian-product probability table is recomputed from the two factor tables. |
| `marginalization-witness` | `sat` | replay-only | The product table's left and right marginals recover the original finite distributions. |
| `finite-fubini-witness` | `sat` | replay-only | One finite direct weighted sum equals both finite iterated sums. |
| `bad-product-measure-rejected` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated contradiction between product mass `1/6` and malformed claim `1/5`. |
| `bad-product-marginal-rejected` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated contradiction between marginal `1/2` and malformed claim `2/3`. |
| `fubini-tonelli-lean-horizon` | `not-run` | lean-horizon | General product-measure construction and Fubini/Tonelli remain future proof-assistant work. |

The checked rows certify only the final exact-linear contradictions after
finite replay computes the product mass or marginal. They do not certify the
general Fubini or Tonelli theorem.

## Finite Fubini Shadow

The finite simple function is listed on the six product atoms:

```text
f(heads, one)   = 1
f(heads, two)   = 2
f(heads, three) = 3
f(tails, one)   = 2
f(tails, two)   = 4
f(tails, three) = 6
```

The direct sum is:

```text
sum_(x,y) f(x,y) R(x,y)
  = (1 + 2 + 3 + 2 + 4 + 6) * (1/6)
  = 3
```

The two iterated finite sums also equal `3`:

```text
sum_x P(x) * sum_y f(x,y) Q(y) = 3
sum_y Q(y) * sum_x f(x,y) P(x) = 3
```

This is a useful bounded shadow because it shows the concrete computation that
Fubini/Tonelli generalizes. The trusted work is only finite rational addition
and multiplication over a fixed table.

## What Is Not Proved Yet

The current finite product-measure resource does not prove:

- existence or uniqueness of product measures on arbitrary sigma-algebras;
- Caratheodory extension, completion, or regularity facts;
- sigma-finite hypotheses or counterexamples when hypotheses fail;
- Tonelli for nonnegative measurable functions;
- Fubini for integrable functions;
- equality of iterated integrals outside finite sums;
- measurability of sections or product functions;
- almost-everywhere equivalence and null-set transport;
- kernels, disintegration, conditional probability, or stochastic-process
  product spaces;
- numerical quadrature, simulation, sampling, or floating-point integration.

Those claims need precise theorem statements, explicit hypotheses, no-`sorry`
Lean artifacts, and an axiom audit before they can graduate from horizon rows.

## Query The Boundary

Find the product-measure Fubini/Tonelli horizon row and its finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-product-measure-v0 \
  --require-any
```

Find Fubini/Tonelli theorem horizons across packs:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text Fubini \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-product-measure-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-product-measure-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each malformed finite claim separately:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-product-measure-v0 \
  --route Farkas \
  --proof-status checked \
  --text bad-product-measure \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-product-measure-v0 \
  --route Farkas \
  --proof-status checked \
  --text bad-product-marginal \
  --require-any
```

## Graduation Criteria

General product-measure and Fubini/Tonelli resources graduate only when they
add:

1. precise Lean theorem statements for product-measure construction, Tonelli,
   Fubini, section measurability, and almost-everywhere product-integral
   equivalence;
2. explicit hypotheses for measurable spaces, sigma-algebras, measures,
   sigma-finiteness, nonnegativity, integrability, null sets, and product
   functions;
3. no-`sorry` proofs with an axiom audit;
4. links from finite product-measure packs to theorem statements as examples,
   not as proof evidence for the theorem;
5. separate numerical-honesty metadata for quadrature, simulation, sampling,
   tolerances, floating-point behavior, or implementation claims;
6. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, product-measure rows remain bounded/computable resources:

```text
untrusted fast search -> proposed finite product table, marginal, iterated sum, or malformed claim
trusted small checking -> exact rational products, finite sums, and Farkas evidence
theorem horizon       -> product-measure construction, Tonelli, Fubini, and a.e. theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-product-measure-v0 --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-product-measure-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-product-measure-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
Fubini/Tonelli row remains `lean-horizon`.
