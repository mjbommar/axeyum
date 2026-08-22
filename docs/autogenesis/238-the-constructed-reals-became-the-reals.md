# The day the constructed reals became the real numbers

Date: 2026-08-22

## What changed

`CReal` is a Bishop setoid of regular ℚ-sequences over the proved ℚ, costing zero
trusted declarations (ADR-0512). On the morning of 2026-08-22 it held **390
theorems and none of the properties that distinguish ℝ from an arbitrary ordered
field**:

```text
archimedean 0 · complete 0 · sup 0 · supremum 0 · cauchy 0 · limit 0 · dense 0
```

Grep-controlled — `mul` 82, `le` 130, `abs` 12 all hit — so those zeros were
real, not a bad query. It proved `mul_one`, `abs_le`, `apart_symm`, `le_congr`,
`Equiv.trans`: an ordered field with an apartness relation, and nothing that made
it ℝ.

By the end of the day it had four, every one `axioms=0`:

| Property | Statement |
|---|---|
| **Archimedean** | `∀ x, ∃ n : Nat, x ≤ ofNat n` |
| **Density of ℚ** | `∀ x n, ∃ q : Rat, x ≤ ofRat (q + 1/(n+1)) ∧ ofRat (q − 1/(n+1)) ≤ x` |
| **Cotransitivity** | `∀ x y, x < y → ∀ z, (x < z) ∨ (z < y)` |
| **Completeness** | `limitSeq_regular : ∀ X, RegularSeq X → Regular (limitSeq X)` and `limit_dist` |

`creal` 390 → 436 theorems; the whole kernel 418 → 464; trusted surface unchanged
at 0 for every prelude except the unreached `axreal`.

## Why each was cheaper than expected

A pattern held across all four, and it is the transferable part: **the
construction already carried more information than the property needed.**

- **Archimedean.** `CReal.bound_within` already bounds `seq x m` by one rational
  at *every* index simultaneously, which is strictly stronger than `CReal.le`'s
  one-inequality-per-index definition asks for. Witness `n := bound x + 1`; no
  case split on sign, no second appeal to ℚ's Archimedean lemma.
- **Density.** The proof avoids `CReal.add`, `neg` and `abs` entirely. Routing
  the difference through `CReal.add` would incur Bishop's `2n+1` shift for no
  benefit, because `CReal.le` against a *directly embedded* rational is already
  pointwise at the same index. Regularity at `(k,n)` gives
  `seq x k − q ≤ 1/(k+1) + 1/(n+1)`, hence
  `seq x k − (q + 1/(n+1)) ≤ 1/(k+1) ≤ 2/(k+1)` — exactly `CReal.le`'s body,
  with slack.
- **Cotransitivity.** No new ℚ lemma at all: the gap splits at an index from
  `Rat.natDivSucc_lt_of_pos` and is compared with `Rat.le_or_lt`, both already
  present. `apart_cotrans` then falls out as a four-way case split on
  `Apart := lt ∨ lt`, with no new estimate.
- **Completeness.** Both obligations close with one hypothesis instantiation plus
  `weaken` against a plain rational inequality — no arbitrary third index, no
  `six_term_bound`, no Archimedean closing lemma, because the hypotheses are
  stated at indices tied to the goal rather than at an arbitrary shared one.

## Two things stated precisely, because the headline over-claims easily

**`RegularSeq` is stated at the diagonal.** It compares `seq (X m) m` against
`seq (X n) n` rather than comparing `X m` and `X n` as reals through
`CReal.add`/`CReal.le` at an arbitrary shared index. `density.rs` proves
`seq (X m) m` is within `1/(m+1)` of `X m`, so bounding one is equivalent **up to
a constant factor** to bounding the other, and re-indexing absorbs the constant.
That is the standard Bishop move — a modulus is a choice — but it is a choice,
and the theorem should be read at the modulus it states.

**`limit_dist` is a rate, not an ε–N existential.** `Equiv (X n) (limit X h)`
would be *false* at finite `n`, so the theorem gives
`|seq (X n) k − seq (limit X h) k| ≤ 2/(k+1) + 2/(n+1)`, uniform in `k`. That is
the substantive checkable content of Bishop's theorem; the existential packaging
follows from it and was not built.

## Why completeness is the one that matters

The other three make ℝ pleasant. Completeness makes analysis *possible*: measure
theory cannot be stated without it, and everything above measure theory —
integration, Lᵖ, martingales, and eventually anything stochastic — is downstream.

For scale, measured against the Mathlib export on disk: ℕ 6,830 declarations,
ℝ 3,254, measure theory and integration 10,937, probability 3,250, martingales
30 — and **Itô's lemma, Brownian motion, the Wiener process and the stochastic
integral do not exist in Mathlib at all**. The formalized frontier stops before
them. So the ladder above us is roughly 40,000 declarations that exist, plus a
stochastic layer that exists nowhere.

We have 464. Completeness is the rung that makes the next one statable.

## Provenance

Four Sonnet subagents, one property each, every result re-measured here from the
kernel before landing rather than accepted from a report. Two of the four
explicitly reported "not confirmed" for figures they had not read out of the
kernel themselves — which is why those landed in minutes rather than needing a
round trip.
