# Lebesgue Integration Theorem Boundary

This page separates Axeyum's finite integration resource from general
Lebesgue-integration, convergence, Fubini/Tonelli, and almost-everywhere
theorem claims.

Primary pack:

- [finite-integration-v0](../../../artifacts/examples/math/finite-integration-v0/)

Companion lessons and maps:

- [End To End: Finite Integration](finite-integration-end-to-end.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Random Variable Theorem Boundary](random-variable-theorem-boundary.md)
- [Stochastic Kernel Theorem Boundary](stochastic-kernel-theorem-boundary.md)
- [Martingale Theorem Boundary](martingale-theorem-boundary.md)

## Current Finite Resource

The pack works over one finite probability space:

```text
P(low)  = 1/4
P(mid)  = 1/4
P(high) = 1/2
```

Its simple function is fixed:

```text
f(low)  = 0
f(mid)  = 2
f(high) = 4
```

The validator recomputes the exact finite weighted sum:

```text
integral f dP = 0*(1/4) + 2*(1/4) + 4*(1/2)
              = 5/2
```

The indicator row fixes the event:

```text
E = {high}
P(E) = 1/2
integral 1_E dP = 1/2
```

The linearity row fixes two simple functions on the same atoms:

```text
f = low:0, mid:2, high:4
g = low:1, mid:1, high:3
integral f dP = 5/2
integral g dP = 2
integral (2*f - g) dP = 3
```

All of this is exact finite rational replay. It is useful measure-theory and
probability table evidence, but it does not construct Lebesgue measure or
prove convergence theorems.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `simple-function-integral-witness` | `sat` | replay-only | The displayed finite simple-function integral is recomputed as `5/2`. |
| `indicator-integral-witness` | `sat` | replay-only | The displayed indicator integral equals the finite event measure `1/2`. |
| `integral-linearity-witness` | `sat` | replay-only | The displayed finite linear combination has integral `3`. |
| `bad-expectation-rejected` | `unsat` | replay-only | Exact replay rejects the false expectation claim `3` after computing `5/2`. |
| `qf-lra-bad-expectation` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated contradiction `integral_value = 5/2` and `integral_value = 3`. |
| `lebesgue-integration-lean-horizon` | `not-run` | lean-horizon | Lebesgue integration and convergence theorems remain future proof-assistant work. |

The checked row is the final exact-linear contradiction after finite replay
computes the expectation. It is not a proof of Lebesgue integration, monotone
convergence, dominated convergence, Fubini/Tonelli, or almost-everywhere
reasoning.

## What Is Not Proved Yet

The current finite integration resource does not prove:

- construction of sigma-algebras, measurable spaces, or Lebesgue measure;
- simple-function approximation for arbitrary measurable functions;
- monotone convergence or dominated convergence;
- Fatou's lemma or convergence in measure/almost everywhere;
- Fubini/Tonelli for general product measures;
- equality of functions or integrals up to null sets;
- Radon-Nikodym or conditional expectation as a general theorem;
- stochastic integration, martingale convergence, or optional stopping;
- numerical quadrature, floating-point integration, simulation quality, or
  statistical-library behavior.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite rows are
examples and regression seeds, not theorem evidence for general measure
theory.

## Query The Boundary

Find the Lebesgue-integration horizon row and its finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-integration-v0 \
  --require-any
```

Find integration-related theorem horizons across packs:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text integration \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-integration-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadow:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-integration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the replay-only bad finite expectation and the checked final
contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-integration-v0 \
  --proof-status replay-only \
  --text expectation \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-integration-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-expectation \
  --require-any
```

## Graduation Criteria

General integration resources graduate only when they add:

1. precise Lean theorem statements for measurable simple functions, integral
   linearity, monotone convergence, dominated convergence, Fatou's lemma,
   Fubini/Tonelli, almost-everywhere equivalence, and product-measure
   integration;
2. explicit hypotheses for sigma-algebras, measures, nonnegativity,
   integrability, measurability, product spaces, null sets, and convergence
   modes;
3. no-`sorry` proofs with an axiom audit;
4. links from finite integration packs to theorem statements as examples, not
   as proof evidence for the theorem;
5. separate numerical-honesty metadata for quadrature, simulation, sampling,
   tolerances, floating-point behavior, or implementation claims;
6. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, integration rows remain bounded/computable resources:

```text
untrusted fast search -> proposed finite expectation, event, linearity, or malformed claim
trusted small checking -> exact rational finite sums and Farkas evidence
theorem horizon       -> Lebesgue integration, convergence, Fubini/Tonelli, and a.e. theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-integration-v0 --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-integration-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-integration-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
Lebesgue-integration row remains `lean-horizon`.
