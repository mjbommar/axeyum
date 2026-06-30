# P2.5 · 00 — Current state: what axeyum's nonlinear engine decides today

Accurate baseline (grounded in the solver source) so every later phase starts
from facts, not aspiration.

## NRA — three layers, all sound, all narrow

### Layer A — single-variable real-root isolation (`crates/axeyum-solver/src/nra_real_root.rs`)

- **Fires when** the whole query is a conjunction `C₁ ∧ … ∧ Cₘ` (flattened
  top-level `and`) where **every** `Cᵢ` normalizes to `pᵢ(x) ⋈ᵢ 0` — a
  **single-variable** real polynomial, the *same* variable `x` across all atoms.
- **Comparators:** `{=, ≠, <, ≤, >, ≥}`.
- **Decides:** equality by isolating real roots (exact rational or irrational
  `RealAlgebraic`); inequalities by sign-cell decomposition (rational sample per
  matching open interval); conjunctions by sign-cell decomposition over all roots.
- **Witnesses:** `Value::Real(Rational)` (exact) or `Value::RealAlgebraic`
  (defining polynomial + isolating interval, refined on comparison).
- **Limits:** declines on ≥2 distinct variables, non-Real sorts, non-polynomial
  ops (`div`, `RealToInt`), non-conjunctive top level (`or`, `=>`), degree > 64,
  coefficient magnitude > 2⁴⁰, any `i128` overflow. **Every `sat` is replayed;
  `unsat` is exact (roots + one sample per open interval cover ℝ).**

### Layer B — linear abstraction + McCormick + branch-and-bound (`nra.rs`)

- **Fires when** Layer A declines. Abstracts each genuinely-nonlinear product
  `a·b` (both operands non-constant) to a fresh variable `r`, yielding a pure-LRA
  relaxation, then refines with **valid product lemmas** (sign, zero, monotonicity,
  shrinking), **sum-of-squares** lemmas `(a±b)² ≥ 0`, **McCormick envelopes**, and
  **spatial branch-and-bound** (split widest interval, depth ≤ 6), with an
  **incremental-linearization point-lemma loop** (≤ 12 rounds).
- **Hard cap:** ≤ 2 distinct-operand cross-products (squares exempt); > 2 →
  `unknown(ResourceLimit)`. This cap exists because multivariate SOS coupling
  drove exact-rational simplex to OOM (measured 3-variable blowup).
- **Soundness:** relaxation only grows the model space ⇒ `unsat` is sound; `sat`
  is replay-checked against originals (failed replay ⇒ decline, never false sat).
  Incomplete by construction.

### Layer C — even-power refutation (`nra_even_power.rs`)

- Syntactic micro-decider: `∑(even-power terms) + nonneg-const < 0` ⇒ `unsat`.
  Pattern-only, not integrated into the main loop.

## NIA — two layers

### Layer A — single-variable integer-polynomial decider (`nia_square.rs`)

- **Fires when** the query is exactly **one** assertion `p(x) ⋈ 0` (single
  variable, `Int`). Degree ≤ 2 by discriminant + convexity; degree ≥ 3 equality /
  disequality by the rational-root theorem (divisor enumeration + Horner). Degree
  ≥ 3 inequalities: declines. Witness `i128`; replay-checked; `unsat` exact.

### Layer B — width-ladder bit-blasting (`auto.rs` nonlinear-int tail)

- `nia_square` → `int_real_relax` (relax Int→Real, NRA `unsat` only, sound) →
  `decide_bounded_int_blast` (provably finite box → exact) →
  `dispatch_int_blast_width_ladder` (try widths `[8,16,32,64]`; first width whose
  SAT model replays is `sat`; else `unknown`). Narrow-first avoids modular
  wrapping producing false models.

## Routing (`crates/axeyum-solver/src/auto.rs`)

```
Real:  decide_real_poly_constraint (Layer A) → check_with_nra (Layer B) → EUF combo / unknown
Int:   linear refuters → nia_square → int_real_relax → bounded blast → width ladder → unknown
```

## Capability-vs-gap table

| Area | Decide today | Assurance | Boundary to close |
|---|---|---|---|
| NRA real-root | 1 variable, deg ≤ 64, conjunctions | replay + exact | **≥ 2 variables**, transcendental |
| NRA abstraction | products (≤ 2 cross), bounded B&B | sound, incomplete | > 2 cross-products, unbounded vars, equational ideals |
| NRA even-power | syntactic sums of even powers < 0 | sound | not integrated |
| NIA 1-var | deg ≤ 2 all cmp; deg ≥ 3 eq/≠ | replay + exact | deg ≥ 3 inequalities, **≥ 2 variables** |
| NIA blast | 8–64-bit ladder, finite box | sound, incomplete | genuine unbounded NIA |

## The one-sentence gap

We decide **single-variable** real/integer polynomial problems exactly and a
**≤2-cross-product** multivariate fragment heuristically; the entire **complete
multivariate QF_NRA decision procedure** (and its NIA descendants) is missing —
that is what Phases A–E build.

## What we can reuse (don't rebuild)

- `axeyum_ir::Rational` (exact i128 rationals; overflow-guarded — see the
  Rational-overflow note in memory) and `Value::RealAlgebraic` (defining poly +
  isolating interval + refinement) **already exist**. Phase A generalizes them to
  multivariate / arbitrary-precision, it does not start from zero.
- The replay/decline discipline, the deadline plumbing, and the differential-fuzz
  harness are all in place.
